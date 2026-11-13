-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_DegreeSums
-- name    : OddOrder_Peterfalvi_S08_DegreeSums
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:26:13.105292+00:00
-- url     : https://prove2.me/theorems/b9c5043b-cdf0-412a-a7e6-bfcb1da90e84
-- title:
--   Peterfalvi §8: base blocks and degree sums
-- statement:
--   Minimal-degree blocks, degree bounds, and character degree-sum identities for Peterfalvi §8.
--
--   Main definitions: `xBaseBlock` (the base block $S_0$: the minimal-real-degree members of $X$), `exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X` (degree-ratio integrality against a base-block anchor), `sMember_degreeSumBound_of_not_coherent` ((6.2) member family to the B1 degree-sum bound), `sum_re_sq_induce_kernelFilter_eq` ((6.2) B2 in real/Frobenius form), `sum_re_sq_Xset_eq` ((6.6) $X$ degree-sum identity, Frobenius case) and `sum_re_sq_Xset_eq_of_irreducible_X` (the CertainType, case (B), form).
--
--   The bundle also proves 17 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_DegreeSums.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_DegreeSums.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_DegreeSums_CoherenceGlue

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(T8 leaf 5) the base block `S₀`**: the minimal-(real-)degree members of `X`.  This is the
equal-minimal-degree prefix `{χ₁,…,χₖ}` of (6.6), on which (1.1)+(1.4) supplies the base coherence
`coherentEqualDegree_fromDade` before the (5.6) adjoining of the strictly-higher-degree conjugate
pairs.  `S₀` must contain **all** minimal-degree members (not just one pair): the first (5.6)
adjoining of a pair of degree ratio `a` needs `2a < ∑_{S₀} aⱼ²`, which fails at equal degree. -/
def xBaseBlock (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  {χ ∈ hyp.Xset Z | ∀ ψ ∈ hyp.Xset Z,
    (OddOrder.Peterfalvi.S03.characterDegree χ).re ≤
      (OddOrder.Peterfalvi.S03.characterDegree ψ).re}

theorem xBaseBlock_subset (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    hyp.xBaseBlock Z ⊆ hyp.Xset Z :=
  fun _ hχ => hχ.1

/-- The minimal-degree base block of `X(Z)` is closed under conjugation.  This uses only the
direct conjugation-invariance of `X(Z)` and degree preservation under conjugation. -/
theorem xBaseBlock_closedUnderConjugate_unconditional
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) := by
  intro χ hχ
  refine ⟨hyp.Xset_closedUnderConjugate_unconditional Z hχ.1, fun ψ hψ => ?_⟩
  have hre : (OddOrder.Peterfalvi.S03.characterDegree χ.conj).re =
      (OddOrder.Peterfalvi.S03.characterDegree χ).re := by
    simp
  rw [hre]
  exact hχ.2 ψ hψ

/-- Any two members of the base block have the same degree (the base is an *equal*-degree family,
the input shape of `coherentEqualDegree_fromDade`). -/
theorem xBaseBlock_degree_re_eq (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.xBaseBlock Z) (hχ' : χ' ∈ hyp.xBaseBlock Z) :
    (OddOrder.Peterfalvi.S03.characterDegree χ).re =
      (OddOrder.Peterfalvi.S03.characterDegree χ').re :=
  le_antisymm (hχ.2 χ' hχ'.1) (hχ'.2 χ hχ.1)

/-- If `χ₁` is a base-block anchor and `χ ∈ X`, then the natural degree of `χ₁` is no larger
than the natural degree of `χ`. -/
theorem natDegree_le_of_xBaseBlock_anchor (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ₁ χ : IrreducibleCharacter ↥L} {d₁ d : ℕ}
    (hχ₁base : (χ₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z)
    (hχX : (χ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hχ₁one : (χ₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hχone : (χ : ClassFunction ↥L ℂ) 1 = (d : ℂ)) :
    d₁ ≤ d := by
  have hre := hχ₁base.2 (χ : ClassFunction ↥L ℂ) hχX
  rw [OddOrder.Peterfalvi.S03.characterDegree_def,
    OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one, hχone] at hre
  exact_mod_cast hre

/-- The base block is closed under conjugation, from the abstract input `X ⊆ Irr L`:
conjugation preserves the degree (`characterDegree_conj`) and `X`
(`Xset_closedUnderConjugate_of_irreducible_X`).  With the no-real property this makes `S₀`
contain a conjugate pair, so `2 ≤ |S₀|`. -/
theorem xBaseBlock_closedUnderConjugate_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (_hZH : Z ≤ H) [Z.Normal]
    (_hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
  hyp.xBaseBlock_closedUnderConjugate_unconditional Z

/-- A member `χ = Ind_H^L θ` of `S` is supported on `H` (its induced character vanishes off the
normal subgroup `H`). -/
theorem sMember_support_subset_H (hyp : SibleyDadeHypothesis G L H)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) :
    χ.support ⊆ (H : Set ↥L) := by
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  rw [hχeq]
  exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)

/-- **(T8 leaf 6) equal-degree difference support.**  For two members `χ, χ'` of `S` of equal
degree (`χ(1) = χ'(1)`) the difference `χ − χ'` is supported on `H^# = sharpImage H`: both are
supported on `H` (`sMember_support_subset_H`) and the difference vanishes at `1` (equal degree).
This is the `hsuppdiff` input of `coherentEqualDegree_fromDade` for the equal-minimal-degree base
block `S₀` (`irreducibleCharacterDifference χ j = χⱼ − χ₀`), and the (5.6) `χ − a·χ₁` support
shape. -/
theorem sMember_diffSupport_of_charValue_eq (hyp : SibleyDadeHypothesis G L H)
    {χ χ' : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hχ'S : χ' ∈ hyp.S) (hdeg : χ 1 = χ' 1) :
    (χ - χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  have hgH : g ∈ H := by
    rcases eq_or_ne (χ g) 0 with hχg | hχg
    · have hχ'g : χ' g ≠ 0 := fun h0 =>
        hg (by rw [ClassFunction.sub_apply, hχg, h0, sub_self])
      exact hyp.sMember_support_subset_H hχ'S (ClassFunction.mem_support.mpr hχ'g)
    · exact hyp.sMember_support_subset_H hχS (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **(T8.11d) scaled degree-matched support.**

For two `S`-members whose degrees satisfy `χ(1) = a χ₁(1)`, the scaled difference
`χ - aχ₁` is supported on `H^# = sharpImage H`.  This is the support bridge used for the
`hmemdegdiffsupp` and `hdiffasuppχ` fields once the integer degree ratios are available. -/
theorem sMember_scaledDiffSupport_of_charValue_eq (hyp : SibleyDadeHypothesis G L H)
    {χ χ' : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hχ'S : χ' ∈ hyp.S) {a : ℕ}
    (hdeg : χ 1 = (a : ℂ) * χ' 1) :
    (χ - a • χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by
      rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ a χ', ClassFunction.smul_apply,
        hdeg, sub_self])
  have hgH : g ∈ H := by
    rcases eq_or_ne (χ g) 0 with hχg | hχg
    · have hχ'g : χ' g ≠ 0 := fun h0 =>
        hg (by
          rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ a χ',
            ClassFunction.smul_apply, hχg, h0, mul_zero, sub_self])
      exact hyp.sMember_support_subset_H hχ'S (ClassFunction.mem_support.mpr hχ'g)
    · exact hyp.sMember_support_subset_H hχS (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **Two-coefficient degree-matched difference support.**  For two `S`-members `χ, χ'` and naturals
`m, n` with `m·χ(1) = n·χ'(1)`, the combination `m·χ − n·χ'` is supported on `H^# = sharpImage H`.
Both are supported on `H` (`sMember_support_subset_H`) and the combination vanishes at `1`.  Unlike
`sMember_scaledDiffSupport_of_charValue_eq` (`χ − a·χ'`, requiring `χ'(1) ∣ χ(1)`), the symmetric
coefficients `m = χ'(1)`, `n = χ(1)` make `m·χ − n·χ'` supported **without** any divisibility — the
(4.1) supported-difference input `χ'(1)·χ − χ(1)·χ'` used in the (6.8.1) `himg_ortho`. -/
theorem sMember_smulDiffSupport_of_charValue_eq (hyp : SibleyDadeHypothesis G L H)
    {χ χ' : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hχ'S : χ' ∈ hyp.S) {m n : ℕ}
    (hdeg : (m : ℂ) * χ 1 = (n : ℂ) * χ' 1) :
    (m • χ - n • χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  have hval : ∀ x : ↥L, (m • χ - n • χ') x = (m : ℂ) * χ x - (n : ℂ) * χ' x := by
    intro x
    rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ m χ, ← Nat.cast_smul_eq_nsmul ℂ n χ',
      ClassFunction.smul_apply, ClassFunction.smul_apply]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [hval, hdeg, sub_self])
  have hgH : g ∈ H := by
    by_contra hgnH
    have hχg : χ g = 0 := by
      by_contra h
      exact hgnH (hyp.sMember_support_subset_H hχS (ClassFunction.mem_support.mpr h))
    have hχ'g : χ' g = 0 := by
      by_contra h
      exact hgnH (hyp.sMember_support_subset_H hχ'S (ClassFunction.mem_support.mpr h))
    exact hg (by rw [hval, hχg, hχ'g, mul_zero, mul_zero, sub_zero])
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **General `S`-combination support from degree 0.**  Any integer combination of `S`-members
(`φ ∈ ℤ[S]`) that vanishes at `1` is supported on `H^# = sharpImage H`.  Each `S`-member is
supported on `H` (`sMember_support_subset_H`), so `φ.support ⊆ H` (span induction); and `φ(1) = 0`
removes `1`.  This is the multi-term generalisation of `sMember_diffSupport_of_charValue_eq` /
`sMember_scaledDiffSupport_of_charValue_eq` — the supported↔degree-0 direction for the `S`-lattice,
the support side of the (6.8.1) `hgen'` decomposition. -/
theorem zSpan_S_support_subset_of_apply_one_eq_zero (hyp : SibleyDadeHypothesis G L H)
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.S) (h1 : φ 1 = 0) :
    φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  -- `ℤ[S] ⊆ {ψ | ψ.support ⊆ H}` by span induction (decoupled from `h1`).
  have hsuppH : ∀ ψ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.S, ψ.support ⊆ (H : Set ↥L) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx => exact hyp.sMember_support_subset_H hx
    | zero => intro g hg; rw [ClassFunction.mem_support] at hg; exact absurd rfl hg
    | add x y _ _ hx hy =>
        intro g hg
        rcases ClassFunction.support_add_subset x y hg with h | h
        · exact hx h
        · exact hy h
    | smul c x _ hx =>
        intro g hg
        refine hx ?_
        rw [ClassFunction.mem_support] at hg ⊢
        intro hxg
        apply hg
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hxg, mul_zero]
  intro g hg
  have hgH : g ∈ H := hsuppH φ hφ hg
  have hg1 : g ≠ 1 := by
    rintro rfl; exact (ClassFunction.mem_support.mp hg) h1
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h => hg1 (OneMemClass.coe_eq_one.mp h)⟩

/-- **`S`-member degree ratio against a degree-`|W₁|` anchor.**

For `χ = Ind_H^L θ ∈ S` and an anchor `χ₁` of the minimal degree `χ₁(1) = |W₁|` (induced from a
degree-`1` source of `H`), the degree ratio `χ(1)/χ₁(1)` is the source degree `θ(1)`, a positive
natural number: `χ(1) = θ(1)·χ₁(1)` (`χ(1) = |L:H|·θ(1) = |W₁|·θ(1)`, `induce_apply_one`).  This
produces the integer degree `a = deg i` and the equation `χ(1) = a·χ₁(1)` that
`sMember_scaledDiffSupport_of_charValue_eq` (and `scaledDiff_dadeImage_mem_ZIrr`) consume for the
`hmemdegdiffsupp`/`hdiffasuppχ`/`htau1_memaχ` fields of the (6.2)/B1 member-family.  Applied with
`χ = χ₁` it gives the anchor ratio `a = 1` (`ha1`). -/
theorem sMember_charValue_one_eq_mul_anchor (hyp : SibleyDadeHypothesis G L H)
    {χ χ₁ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ)) :
    ∃ a : ℕ, 0 < a ∧ χ 1 = (a : ℂ) * χ₁ 1 := by
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  obtain ⟨a, ha_pos, ha⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  refine ⟨a, ha_pos, ?_⟩
  rw [hχeq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, ha,
    hyp.index_H_eq_card_W1, hχ₁deg]
  ring

open scoped Classical in
/-- **Degree-ratio integrality against a base-block anchor.**  For `χ ∈ X(Z)` and a minimal-degree
anchor `χ₁ ∈ xBaseBlock Z`, the degree ratio `χ(1)/χ₁(1)` is a positive natural number:
`∃ d : ℕ, 0 < d ∧ χ(1) = d·χ₁(1)`.  Both source degrees are powers of `p` (`H` a `p`-group,
`IsIrreducibleCharacter.exists_charValue_one_eq_prime_pow_of_isPGroup`); minimality
(`natDegree_le_of_xBaseBlock_anchor`) gives `χ₁(1) ≤ χ(1)`, so the smaller `p`-power divides the
larger and the ratio `p^{k−k₁}` is a positive integer.  This is the `dᵢ ∈ ℤ` datum of the (6.8.1)
`hgen'` decomposition (the degree side; `zSpan_S_support_subset_of_apply_one_eq_zero` is the support
side).

Only `X`-irreducibility (`hX`) is used from the ambient hypothesis, so this form serves both the
Frobenius case (`exists_charValue_one_eq_mul_xBaseBlock_anchor`) and case (A) / c2 (where `hX` is
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`). -/
theorem exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) {Z : Subgroup ↥L}
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {χ χ₁ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) (hχ₁base : χ₁ ∈ hyp.xBaseBlock Z) :
    ∃ d : ℕ, 0 < d ∧ χ 1 = (d : ℂ) * χ₁ 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  -- sources of `χ` and `χ₁`.
  have hχS : χ ∈ hyp.S := hyp.Xset_subset_S hχX
  have hχ₁S : χ₁ ∈ hyp.S := hyp.Xset_subset_S (hyp.xBaseBlock_subset Z hχ₁base)
  rw [hyp.S_eq] at hχS hχ₁S
  obtain ⟨θ, -, hχeq⟩ := hχS
  obtain ⟨θ₁, -, hχ₁eq⟩ := hχ₁S
  obtain ⟨a, ha_pos, ha⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  obtain ⟨a₁, ha₁_pos, ha₁⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ₁
  -- source degrees are `p`-powers.
  obtain ⟨k, hk⟩ := θ.2.exists_charValue_one_eq_prime_pow_of_isPGroup hHp
  obtain ⟨k₁, hk₁⟩ := θ₁.2.exists_charValue_one_eq_prime_pow_of_isPGroup hHp
  have hak : a = p ^ k := by exact_mod_cast ha.symm.trans hk
  have ha₁k₁ : a₁ = p ^ k₁ := by exact_mod_cast ha₁.symm.trans hk₁
  -- `χ(1) = |W₁|·a`, `χ₁(1) = |W₁|·a₁` (nat degrees).
  have hχ1 : χ 1 = ((Nat.card hyp.W1 * a : ℕ) : ℂ) := by
    rw [hχeq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, ha,
      hyp.index_H_eq_card_W1]; push_cast; ring
  have hχ₁1 : χ₁ 1 = ((Nat.card hyp.W1 * a₁ : ℕ) : ℂ) := by
    rw [hχ₁eq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, ha₁,
      hyp.index_H_eq_card_W1]; push_cast; ring
  -- minimality of `χ₁`: `|W₁|·a₁ ≤ |W₁|·a`, hence `a₁ ≤ a`, hence `k₁ ≤ k`.
  have hirr : IsIrreducibleCharacter χ := hX χ hχX
  have hirr₁ : IsIrreducibleCharacter χ₁ := hX χ₁ (hyp.xBaseBlock_subset Z hχ₁base)
  have hle : Nat.card hyp.W1 * a₁ ≤ Nat.card hyp.W1 * a :=
    hyp.natDegree_le_of_xBaseBlock_anchor (χ₁ := ⟨χ₁, hirr₁⟩) (χ := ⟨χ, hirr⟩) hχ₁base hχX hχ₁1 hχ1
  have hW1pos : 0 < Nat.card hyp.W1 := Nat.card_pos
  have ha₁a : a₁ ≤ a := Nat.le_of_mul_le_mul_left hle hW1pos
  have hkk₁ : k₁ ≤ k := by
    rw [hak, ha₁k₁] at ha₁a; exact (Nat.pow_le_pow_iff_right hp.one_lt).mp ha₁a
  -- the ratio is `p^{k−k₁}`.
  refine ⟨p ^ (k - k₁), pow_pos hp.pos _, ?_⟩
  have hap : a = p ^ (k - k₁) * a₁ := by rw [hak, ha₁k₁, ← pow_add]; congr 1; omega
  rw [hχ1, hχ₁1]
  have : Nat.card hyp.W1 * a = p ^ (k - k₁) * (Nat.card hyp.W1 * a₁) := by rw [hap]; ring
  rw [this]; push_cast; ring

/-- **(6.2) member-family core for `S₁ ⊆ S`** (Frobenius case): the flat enumeration of `S₁` with
its per-member orthonormality, non-realness, conjugate-difference support, and `S₁`-membership
facts.

For a finite conjugation-closed `S₁ ⊆ S`, `exists_finEnum_irreducible` gives an injective family
`χmem : Fin k → Irr L` with range `S₁`; the per-member helpers (`sMember_characterFacts`,
`sMember_diffSupport`) and conjugation-closure of `S₁` discharge the `hmemreal`/`hmemconjortho`/
`hmemortho`/`hmemdiffsupp`/`hmemS1`/`hmembarS1` fields that B1
(`coherentDegreeSumBound_of_not_coherent`) consumes.  The degree data
(`deg`/`hmemdegdiffsupp`, from `sMember_charValue_one_eq_mul_anchor`) is layered on separately. -/
theorem exists_sMemberOrthonormalFamily (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ)) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁) ∧
      (∀ j, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0) ∧
      (∀ i j, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ) = if i = j then (1 : ℂ) else 0) := by
  have hS₁irr : ∀ φ ∈ S₁, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hS₁sub hφ)
  obtain ⟨k, χmem, hχinj, hrange⟩ := exists_finEnum_irreducible hS₁fin hS₁irr
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact Set.mem_range_self j
  refine ⟨k, χmem, hχinj, hrange, ?_, ?_, hmemS1, ?_, ?_, ?_⟩
  · intro j
    exact (hyp.sMember_characterFacts hF (hS₁sub (hmemS1 j))).1
  · intro j
    exact hyp.sMember_diffSupport (hS₁sub (hmemS1 j)) (χmem j).2
  · intro j
    exact hS₁conj (hmemS1 j)
  · intro j
    exact (hyp.sMember_characterFacts hF (hS₁sub (hmemS1 j))).2.2.2.2
  · intro i j
    rw [irreducibleCharacter_inner_eq_ite (χmem i) (χmem j)]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · rw [if_neg (fun he => h (hχinj he)), if_neg h]

/-- **(6.2) member-family degree data** (Frobenius case): integer degree ratios against a
degree-`|W₁|` anchor.

Given a family `χmem` of `S`-members and a distinguished index `i₁` whose member has the minimal
degree `χmem i₁ (1) = |W₁|`, every member has a positive integer degree ratio
`χmem j (1) = (deg j)·χmem i₁ (1)` (the source degree, `sMember_charValue_one_eq_mul_anchor`), the
anchor ratio is `deg i₁ = 1` (cancel the nonzero `|W₁|`), and each scaled difference
`χmem j − deg j·χmem i₁` is supported on `H^#` (`sMember_scaledDiffSupport_of_charValue_eq`).  This
is the `deg`/`ha1`/`hmemdegdiffsupp` data that layers on `exists_sMemberOrthonormalFamily` to
complete the (6.2)/B1 member-family. -/
theorem exists_sMemberDegreeData (hyp : SibleyDadeHypothesis G L H)
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L} {i₁ : Fin k}
    (hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.S)
    (hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (Nat.card hyp.W1 : ℂ)) :
    ∃ deg : Fin k → ℕ, deg i₁ = 1 ∧ (∀ j, 0 < deg j) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 =
        (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ) - deg j • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  choose deg hdeg_pos hdeg_eq using fun j =>
    hyp.sMember_charValue_one_eq_mul_anchor (hmemS j) hanchordeg
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨deg, ?_, hdeg_pos, hdeg_eq, fun j =>
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hmemS j) (hmemS i₁) (hdeg_eq j)⟩
  have h := hdeg_eq i₁
  rw [hanchordeg] at h
  have hdeg1 : (deg i₁ : ℂ) = 1 :=
    mul_right_cancel₀ hW1ne (by rw [one_mul]; exact h.symm)
  exact_mod_cast hdeg1

/-- **(6.2) anchor existence: `S(A)` contains a member of the minimal degree `|W₁|`.**

When the section `H/(A.subgroupOf H)` has a proper commutator subgroup (e.g. `A ⊊ H` with `H`
solvable, so `H/A` is a nontrivial solvable group), it carries a nontrivial degree-`1` character
trivial on `A` (`exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top`); its
induction `Ind_H^L θ ∈ S(A)` has degree `|L:H|·1 = |W₁|`
(`induce_apply_one_eq_card_W1_of_degree_one`).  This furnishes the degree-`|W₁|` anchor `χ₁`
consumed by `exists_sMemberDegreeData` (its `hanchordeg`). -/
theorem exists_mem_SsubFiltration_degree_W1 (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {A : Subgroup ↥L} [A.Normal]
    (h : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤) :
    ∃ φ, φ ∈ hyp.SsubFiltration A ∧ (φ : ClassFunction ↥L ℂ) 1 = (Nat.card hyp.W1 : ℂ) := by
  obtain ⟨θ, hθne, hθker, hθdeg⟩ :=
    exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top (A.subgroupOf H) h
  refine ⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), ?_, ?_⟩
  · rw [hyp.mem_SsubFiltration]; exact ⟨θ, hθne, hθker, rfl⟩
  · exact hyp.induce_apply_one_eq_card_W1_of_degree_one θ hθdeg

/-- **(6.2) adjoined-pair fields for the breaking pair `{ψ, ψ̄}`** (Frobenius case).

For `ψ ∈ S` whose conjugate pair `{ψ, ψ̄}` is disjoint from `S₁ ⊆ S`, this packages the per-`ψ`
fields B1 (`coherentDegreeSumBound_of_not_coherent`) consumes: non-realness and orthonormality of
`{ψ, ψ̄}` (`sMember_characterFacts`), the conjugate-difference support on `H^#`
(`sMember_diffSupport`), and the orthogonality of `ψ` and `ψ̄` to every member of `S₁` (distinct
irreducibles, since `ψ, ψ̄ ∉ S₁` but the members lie in `S₁`).  Together with
`exists_coherentBreakPair` (which supplies `ψ ∉ S₁`, `ψ̄ ∉ S₁`) this is the adjoined-pair side of
the (6.2) member-family. -/
theorem sBreakPair_fields (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {ψ : ClassFunction ↥L ℂ} {S₁ : Set (ClassFunction ↥L ℂ)}
    (hψS : ψ ∈ hyp.S) (hS₁sub : S₁ ⊆ hyp.S) (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁) :
    ¬ ClassFunction.IsReal ψ ∧
      ClassFunction.inner ψ ψ = 1 ∧ ClassFunction.inner ψ.conj ψ.conj = 1 ∧
      ClassFunction.inner ψ.conj ψ = 0 ∧ ClassFunction.inner ψ ψ.conj = 0 ∧
      ((ψ.conj - ψ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ χ = 0) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ.conj χ = 0) := by
  have hψirr : IsIrreducibleCharacter ψ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS
  obtain ⟨hreal, hψψ, hψbarψbar, hψbarψ, hψψbar⟩ := hyp.sMember_characterFacts hF hψS
  refine ⟨hreal, hψψ, hψbarψbar, hψbarψ, hψψbar,
    hyp.sMember_diffSupport hψS hψirr, ?_, ?_⟩
  · intro χ hχS1
    have hχirr : IsIrreducibleCharacter χ :=
      hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hS₁sub hχS1)
    have hne : ψ ≠ χ := fun h => hψnotS1 (by rw [h]; exact hχS1)
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hψirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hχirr⟩
    rwa [if_neg (fun he => hne (congrArg Subtype.val he))] at h
  · intro χ hχS1
    have hχirr : IsIrreducibleCharacter χ :=
      hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hS₁sub hχS1)
    have hne : ψ.conj ≠ χ := fun h => hψcnotS1 (by rw [h]; exact hχS1)
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ.conj, hψirr.conj⟩ : IrreducibleCharacter ↥L)
      ⟨χ, hχirr⟩
    rwa [if_neg (fun he => hne (congrArg Subtype.val he))] at h

/-- **(T8.11e) scaled supported differences map to virtual characters.**

Once the degree-ratio support field for `χ - aχ₁` is known, the real Dade map sends that
scaled difference to `ℤ[Irr G]`.  This is exactly the `htau1_memaχ` field of
`XAdjoinStepInput`, separated from the arithmetic that produces the ratio and support. -/
theorem scaledDiff_dadeImage_mem_ZIrr (hyp : SibleyDadeHypothesis G L H)
    {χ χ₁ : IrreducibleCharacter ↥L} {a : ℕ}
    (hdiffasupp : ((χ : ClassFunction ↥L ℂ) - a • (χ₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    hyp.tau ((χ : ClassFunction ↥L ℂ) - a • (χ₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G := by
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dade hdiffasupp
    (Submodule.sub_mem _ χ.mem_ZIrr (nsmul_mem χ₁.mem_ZIrr a))

open scoped Classical in
/-- **(6.2) member-family → B1 degree-sum bound.**

Assembles the (6.2) member-family for a coherent `S₁` and the breaking pair `{ψ, ψ̄}`, feeding it to
B1 (`coherentDegreeSumBound_of_not_coherent`).  When `S₁` (conjugation-closed, coherent, `⊆ S`)
contains the degree-`|W₁|` anchor `χ₁`, `ψ ∈ S` with `{ψ, ψ̄}` disjoint from `S₁`, and
`S₁ ∪ {ψ, ψ̄}`
is not coherent, the degree-ratio sum is bounded by `∑ⱼ (degⱼ)² ≤ 2·a`, where `degⱼ = χⱼ(1)/χ₁(1)`
and `a = ψ(1)/χ₁(1)`.

All member-family fields are discharged from the landed pieces: the per-member core
(`exists_sMemberOrthonormalFamily`), the degree data (`exists_sMemberDegreeData`), the adjoined-pair
fields (`sBreakPair_fields`), the scaled-difference support + Dade image
(`sMember_scaledDiffSupport_of_charValue_eq`, `scaledDiff_dadeImage_mem_ZIrr`), and the abstract
S07 generation bridges (`…_scaledDiffs`, `…_anchorGeneration`).  This is the (6.2) step
"`2ψ(1)|L:K| ≥ ∑_{χ∈S₁} χ(1)²/‖χ‖²`" in normalized integer form. -/
theorem sMember_degreeSumBound_of_not_coherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L) (deg : Fin k → ℕ) (a : ℕ),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (deg j : ℂ) * χ₁ 1) ∧
      ψ 1 = (a : ℂ) * χ₁ 1 ∧
      ∑ j : Fin k, ((deg j : ℝ)) ^ 2 ≤ 2 * (a : ℝ) := by
  classical
  -- (1) enumerate `S₁` with the per-member fields
  obtain ⟨k, χmem, hχinj, hrange, hmemreal, hmemdiffsupp, hmemS1, hmembarS1,
    hmemconjortho, hmemortho⟩ := hyp.exists_sMemberOrthonormalFamily hF hS₁sub hS₁conj hS₁fin
  -- (2) locate the anchor index `i₁` (the anchor lies in `S₁ = range χmem`)
  have hχ₁range : χ₁ ∈ Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) := by
    rw [hrange]; exact hχ₁S₁
  obtain ⟨i₁, hi₁eq0⟩ := hχ₁range
  have hi₁eq : (χmem i₁ : ClassFunction ↥L ℂ) = χ₁ := hi₁eq0
  have hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.S := fun j => hS₁sub (hmemS1 j)
  have hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (Nat.card hyp.W1 : ℂ) := by
    rw [hi₁eq]; exact hχ₁deg
  -- (3) degree data
  obtain ⟨deg, hdeg_i₁, _hdeg_pos, hdeg_eq, hmemdegdiffsupp⟩ :=
    hyp.exists_sMemberDegreeData hmemS hanchordeg
  -- (4) breaking-pair fields
  obtain ⟨hrealψ, hψψ, hψbarψbar, hψbarψ, hψψbar, hdiffsuppψ, hψ_S1, hψbar_S1⟩ :=
    hyp.sBreakPair_fields hF hψS hS₁sub hψnotS1 hψcnotS1
  -- (5) the `ψ` degree ratio `a`
  obtain ⟨a, _ha_pos, hψratio⟩ := hyp.sMember_charValue_one_eq_mul_anchor hψS hanchordeg
  -- (6) `ψ` scaled-difference support + Dade image (the `ψ`-side `hdiffasuppχ`/`htau1_memaχ`)
  have hdiffasuppψ : (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq hψS (hmemS i₁) hψratio
  have htau1ψ : hyp.tau (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G :=
    hyp.scaledDiff_dadeImage_mem_ZIrr (χ := ⟨ψ, hψirr⟩) (χ₁ := χmem i₁) hdiffasuppψ
  -- (7) generation fields via the abstract S07 bridges (`hSgen`, `hgen`)
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧
      (χmem j : ClassFunction ↥L ℂ) = x := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen := OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
    (s := (Finset.univ : Finset (Fin k))) (χmem := fun j => (χmem j : ClassFunction ↥L ℂ))
    (deg := deg) (i₁ := i₁) hcover (Finset.mem_univ i₁) (fun j _ => hmemS1 j)
    (fun j _ => hmemdegdiffsupp j)
  have hbar1 : ψ.conj 1 = ψ 1 := by
    rw [ClassFunction.conj_apply]
    obtain ⟨n, -, hn1, -⟩ := hψirr.exists_natDegree_charValue_one_dvd_card
    rw [hn1, star_natCast]
  have hchi1_ne : (χmem i₁ : ClassFunction ↥L ℂ) 1 ≠ 0 := by
    rw [hanchordeg]; exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    intro hmem
    exact hmem.2 (by simp)
  have hgen := OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
    (χ := ψ) (chibar := ψ.conj) (chi1 := (χmem i₁ : ClassFunction ↥L ℂ)) (a := a)
    hSgen hψratio hbar1 hchi1_ne h1A
  -- (8) feed everything to B1
  refine ⟨k, χmem, deg, a, hχinj, hrange, fun j => by rw [hdeg_eq j, hi₁eq],
    by rw [hψratio, hi₁eq], ?_⟩
  have hbound := coherentDegreeSumBound_of_not_coherent hyp.dade hS₁coh
    ⟨ψ, hψirr⟩ hrealψ hdiffsuppψ hψψ hψbarψbar hψψbar hψbarψ hψ_S1 hψbar_S1
    (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁)
    (fun j _ => hmemreal j) (fun j _ => hmemdiffsupp j) (fun j _ => hmemdegdiffsupp j)
    (fun j _ => hmemS1 j) (fun j _ => hmembarS1 j) (fun j _ => hmemconjortho j)
    (fun i _ j _ => by rw [hmemortho i j]; rcases eq_or_ne i j with h | h <;> simp [h])
    hdiffasuppψ htau1ψ hdeg_i₁ hSgen hgen hnc
  simpa using hbound

/-- **(6.2) member-family degree-square bound** (real form).

The degree-sum bound `sMember_degreeSumBound_of_not_coherent` (`∑ⱼ (degⱼ)² ≤ 2a`), rescaled by the
anchor degree `χ₁(1) = |W₁|`, gives the character-degree-square sum over the enumerated `S₁`-family:
`∑ⱼ (χⱼ(1))² ≤ 2·ψ(1)·χ₁(1)` (real parts), since `χⱼ(1) = degⱼ·χ₁(1)` and `ψ(1) = a·χ₁(1)`.  This is
the (6.2) bound `∑_{χ∈S₁} χ(1)² ≤ 2ψ(1)χ₁(1)` in the form ready to be compared, via `S(A) ⊆ S₁`,
with the `S(A)` degree-sum identity B2. -/
theorem sMember_degreeSqReBound_of_not_coherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 ≤
        2 * (ψ 1).re * (χ₁ 1).re := by
  obtain ⟨k, χmem, deg, a, hχinj, hrange, hdeg_eq, hψ_eq, hbound⟩ :=
    hyp.sMember_degreeSumBound_of_not_coherent hF hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁ hχ₁deg
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact ⟨j, rfl⟩
  refine ⟨k, χmem, hχinj, hrange, hmemS1, ?_⟩
  -- real parts of the degree relations
  have hdegre : ∀ j, ((χmem j : ClassFunction ↥L ℂ) 1).re = (deg j : ℝ) * (χ₁ 1).re := by
    intro j
    rw [hdeg_eq j, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  have hψre : (ψ 1).re = (a : ℝ) * (χ₁ 1).re := by
    rw [hψ_eq, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  have hre_nonneg : (0 : ℝ) ≤ (χ₁ 1).re ^ 2 := sq_nonneg _
  calc ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2
      = ∑ j : Fin k, ((deg j : ℝ) * (χ₁ 1).re) ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hdegre j]
    _ = (χ₁ 1).re ^ 2 * ∑ j : Fin k, (deg j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    _ ≤ (χ₁ 1).re ^ 2 * (2 * (a : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hbound hre_nonneg
    _ = 2 * ((a : ℝ) * (χ₁ 1).re) * (χ₁ 1).re := by ring
    _ = 2 * (ψ 1).re * (χ₁ 1).re := by rw [hψre]

open scoped Classical in
/-- **(6.2) B2 in real / Frobenius form.**

In the Frobenius case every member of `S(A)` is an irreducible induced character
(`isIrreducibleCharacter_of_mem_S_of_frobenius`), so `χ(1)²/‖χ‖² = (χ(1).re)²` (`‖χ‖² = 1`, `χ(1)`
a real natural number), and B2 (`sum_div_normSq_induce_kernelFilter_eq`) becomes the real
degree-square identity `∑_{χ∈S(A)} (χ(1).re)² = |L:H|·(|H:A| − 1)`. -/
theorem sum_re_sq_induce_kernelFilter_eq (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {A : Subgroup ↥L} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
        ((χ 1).re) ^ 2
      = (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) := by
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  have hB2 := sum_div_normSq_induce_kernelFilter_eq (G := ↥L) (H := H) (A := A)
  have hsummand : ∀ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
      (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥H ℂ) ∧
        θ ≠ trivialIrreducibleCharacter ↥H)).image
      (fun θ => ClassFunction.induce H θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ = ((((χ 1).re) ^ 2 : ℝ) : ℂ) := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    have hθne : θ ≠ trivialIrreducibleCharacter ↥H := (Finset.mem_filter.mp hθ).2.2
    have hχS : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ∈ hyp.S := by
      rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩
    have hirr := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hχS
    have hinner : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite (⟨_, hirr⟩ : IrreducibleCharacter ↥L) ⟨_, hirr⟩
    obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
    rw [hinner, div_one, hn1, Complex.natCast_re]; push_cast; ring
  have key : ((∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
        ((χ 1).re) ^ 2 : ℝ) : ℂ)
      = (((H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hsummand χ hχ).symm), hB2]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

open scoped Classical in
/-- **(6.6) X degree-sum identity (Frobenius case).**

The degree-square sum over `X = S − S(Z)` is `|L:H| · (|H| − |H:Z|)`.  Since `S = S(⊥)` and
`S(Z) ⊆ S`, this is the difference of two instances of the `S(A)` degree-sum identity
`sum_re_sq_induce_kernelFilter_eq` (at `A = ⊥`, using `|H ⧸ ⊥| = |H|`, and at `A = Z`).  This is
the `total` of the X-chain step data: the (6.6) divisibility argument shows the source degree
`θχ(1)²` divides it. -/
theorem sum_re_sq_Xset_eq (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {Z : Subgroup ↥L} [Z.Normal] :
    ∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        ((χ 1).re) ^ 2
      = (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
  let : H.Normal := hyp.H_normal
  have hbotker : ∀ θ : IrreducibleCharacter ↥H,
      (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro θ x hx
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hsub : (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) ⊆
      (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) := by
    apply Finset.image_subset_image
    intro θ hθ
    rw [Finset.mem_filter] at hθ ⊢
    exact ⟨hθ.1, hbotker θ, hθ.2.2⟩
  have hsd := Finset.sum_sdiff (f := fun χ : ClassFunction ↥L ℂ => ((χ 1).re) ^ 2) hsub
  have h0 := hyp.sum_re_sq_induce_kernelFilter_eq hF (A := (⊥ : Subgroup ↥L))
  have hZ := hyp.sum_re_sq_induce_kernelFilter_eq hF (A := Z)
  have hbotcard : Nat.card (↥H ⧸ (⊥ : Subgroup ↥L).subgroupOf H) = Nat.card ↥H := by
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥H)).toEquiv
  rw [hbotcard] at h0
  rw [eq_sub_of_add_eq hsd, h0, hZ]
  ring

open scoped Classical in
/-- **(6.6) X degree-sum identity, CertainType (case B) form.**  The Frobenius proof
(`sum_re_sq_Xset_eq`) routes the degree-square sum over `X = S − S(Z)` through
`sum_re_sq_induce_kernelFilter_eq`, which converts each summand `χ(1)²/‖χ‖² = (χ(1).re)²`
using that **every** member of `S` is irreducible (Frobenius).  In case B `S` carries `w₂−1`
reducible members, so that conversion fails on `S`.  But `X` itself is irreducible
(Peterfalvi (6.8.1) for (c2): the reducibles all lie in `S(Z)`, and `X = S ∖ S(Z)`), so the
conversion holds **on `X`** alone. The orbit-counting identity
`sum_div_normSq_induce_kernelFilter_eq`
(in the `χ(1)²/‖χ‖²` form — valid for reducibles) supplies the two filter sums, and
`Finset.sum_sdiff` extracts `∑_X = ∑_{S} − ∑_{S(Z)}`; the `X`-irreducibility hypothesis converts
only the `X`-side terms.  This unblocks the case-B (CB3 math-A / CB4 math-B) `hstepData` `total`. -/
theorem sum_re_sq_Xset_eq_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} [Z.Normal]
    (hX : ∀ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        IsIrreducibleCharacter χ) :
    ∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        ((χ 1).re) ^ 2
      = (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  have hbotker : ∀ θ : IrreducibleCharacter ↥H,
      (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro θ x hx
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hsub : (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) ⊆
      (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) := by
    apply Finset.image_subset_image
    intro θ hθ
    rw [Finset.mem_filter] at hθ ⊢
    exact ⟨hθ.1, hbotker θ, hθ.2.2⟩
  have hsd := Finset.sum_sdiff
    (f := fun χ : ClassFunction ↥L ℂ => χ 1 ^ 2 / ClassFunction.inner χ χ) hsub
  have hB2bot := sum_div_normSq_induce_kernelFilter_eq (G := ↥L) (H := H) (A := (⊥ : Subgroup ↥L))
  have hB2Z := sum_div_normSq_induce_kernelFilter_eq (G := ↥L) (H := H) (A := Z)
  have hbotcard : Nat.card (↥H ⧸ (⊥ : Subgroup ↥L).subgroupOf H) = Nat.card ↥H := by
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥H)).toEquiv
  rw [hbotcard] at hB2bot
  have hconv : ∀ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) \
      (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction)),
      χ 1 ^ 2 / ClassFunction.inner χ χ = ((((χ 1).re) ^ 2 : ℝ) : ℂ) := by
    intro χ hχ
    have hirr := hX χ hχ
    have hinner : ClassFunction.inner χ χ = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)
        ⟨χ, hirr⟩
    obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
    rw [hinner, div_one, hn1, Complex.natCast_re]
    push_cast; ring
  have key : ((∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        ((χ 1).re) ^ 2 : ℝ) : ℂ)
      = (((H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ))) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hconv χ hχ).symm),
      eq_sub_of_add_eq hsd, hB2bot, hB2Z]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08


