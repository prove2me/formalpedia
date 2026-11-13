-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeClifford
-- name    : OddOrder_Peterfalvi_S06_CertainTypeClifford
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:05:39.643208+00:00
-- url     : https://prove2.me/theorems/e4985bac-8e51-4b7f-a60e-c0115efb3686
-- title:
--   Peterfalvi §6 (4.5): Clifford theory of the certain-type characters
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, pp. 21-24, formalizing (4.5): the column sums $\mu_j=\sum_i\mu_{ij}$ and the restrictions $\chi_j$ of the certain-type character family of (4.3.b), using its kernel description from (4.4).
--
--   The key results are the (4.5.b) fixed-class lemmas `conjClass_meets_W2`, `card_fixed_conjClasses_le_W2` and `card_fixed_irr_le_W2` (an element $g$ fixes at most $w_2$ irreducibles), together with `mem_W2_of_mem_sup_of_mem_K` ($W\cap K=W_2$) and nonnegativity and genuineness facts for induced characters.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S06_CertainTypeClifford.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_CertainTypeClifford.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeCharacters

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S05

section GroupActionInfra

/-- A free action of a finite group `G` on a finite type `α` has `|G| ∣ |α|`. -/
theorem card_group_dvd_card_of_freeAction {G α : Type*} [Group G] [Finite G] [Finite α]
    [MulAction G α] (hfree : ∀ (s : G) (a : α), s • a = a → s = 1) :
    Nat.card G ∣ Nat.card α := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype α := Fintype.ofFinite α
  have : ∀ s : G, Fintype (MulAction.fixedBy α s) := fun _ => Fintype.ofFinite _
  have : Fintype (MulAction.orbitRel.Quotient G α) := Fintype.ofFinite _
  have key := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G α
  have h0 : ∀ s ∈ (Finset.univ : Finset G), s ≠ 1 →
      Fintype.card (MulAction.fixedBy α s) = 0 := by
    intro s _ hs
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun a => hs (hfree s (a : α) (MulAction.mem_fixedBy.mp a.2))⟩
  have h1 : Fintype.card (MulAction.fixedBy α (1 : G)) = Fintype.card α := by
    have huniv : MulAction.fixedBy α (1 : G) = Set.univ := by
      ext a; simp
    exact Fintype.card_congr ((Equiv.setCongr huniv).trans (Equiv.Set.univ α))
  have hsum : (∑ s : G, Fintype.card (MulAction.fixedBy α s)) = Fintype.card α :=
    (Finset.sum_eq_single (1 : G) h0 (fun h => absurd (Finset.mem_univ _) h)).trans h1
  rw [hsum] at key
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact ⟨Fintype.card (MulAction.orbitRel.Quotient G α), by rw [key]; ring⟩

end GroupActionInfra

section CharacterInfra

variable {G : Type*} [Group G]

/-- The restriction `Res^G_H φ` of a genuine character is genuine (cf. `S08.isCharacter_restrict`).
The witnessing representation `ρ` of `φ` restricts to `ρ.comp H.subtype` on `H`. -/
theorem isCharacter_restrict [Finite G] {φ : ClassFunction G ℂ}
    (hφ : IsCharacter φ) (H : Subgroup G) :
    IsCharacter (ClassFunction.restrict H φ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hφ
  have hφeq : φ = repCharacterClassFunction ρ :=
    ClassFunction.ext fun g => by rw [repCharacterClassFunction_apply]; exact congrFun hρ g
  rw [hφeq, ClassFunction.restrict_repCharacterClassFunction H ρ]
  exact repCharacterClassFunction_isCharacter (ρ.comp H.subtype)

open scoped ComplexOrder in
/-- The inner product of two genuine characters is `≥ 0` (cf. `S08.inner_isCharacter_nonneg`).
Decompose the right argument into a non-negative integer combination of irreducibles; each
summand `⟨χ, a⟩` is `≥ 0` by `inner_irreducible_nonneg`. -/
theorem inner_isCharacter_nonneg [Fintype G] [Invertible (Nat.card G : ℂ)]
    {χ ψ : ClassFunction G ℂ} (hχ : IsCharacter χ) (hψ : IsCharacter ψ) :
    0 ≤ ClassFunction.inner χ ψ := by
  obtain ⟨m, hsupp, hsum, _⟩ := hψ.exists_natFinsupp_eq_sum
  rw [hsum, inner_sum_right]
  refine Finset.sum_nonneg fun a ha => ?_
  have ha' : IsIrreducibleCharacter a :=
    mem_irreducibleCharacters.mp (hsupp (Finset.mem_coe.mpr ha))
  rw [OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  exact mul_nonneg (Nat.cast_nonneg _) (hχ.inner_irreducible_nonneg ha')

set_option linter.unusedFintypeInType false in
open scoped ComplexOrder in
/-- The induced character `Ind_H^G θ` of a genuine character decomposes as a non-negative integer
combination of irreducibles, with multiplicity `⟨Ind θ, ψ⟩` at `ψ ∈ Irr G`
(cf. `S08.induce_exists_natFinsupp_eq_sum`).  Reconstructed from `Ind θ ∈ ZIrr G`
(`induce_mem_ZIrr`) plus the non-negativity of `⟨Ind θ, ψ⟩ = ⟨θ, Res ψ⟩` (Frobenius reciprocity
and `inner_isCharacter_nonneg`), pushed through `Int.toNat`. -/
theorem induce_exists_natFinsupp_eq_sum [Fintype G]
    [Invertible (Nat.card G : ℂ)] {H : Subgroup G} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] {θ : ClassFunction ↥H ℂ} (hθ : IsCharacter θ) :
    ∃ m : ClassFunction G ℂ →₀ ℕ, (↑m.support ⊆ irreducibleCharacters G) ∧
      ClassFunction.induce H θ = ∑ a ∈ m.support, (m a : ℂ) • a ∧
      ∀ ψ : ClassFunction G ℂ, IsIrreducibleCharacter ψ →
        (m ψ : ℂ) = ClassFunction.inner (ClassFunction.induce H θ) ψ := by
  classical
  obtain ⟨c, hsupp, hsum⟩ := mem_ZIrr_repr (ClassFunction.induce_mem_ZIrr H hθ.mem_ZIrr)
  have hcoeff : ∀ ψ : ClassFunction G ℂ, ψ ∈ irreducibleCharacters G →
      (c ψ : ℂ) = ClassFunction.inner (ClassFunction.induce H θ) ψ := by
    intro ψ hψ
    have h := inner_eq_coeff_of_repr (⟨ψ, hψ⟩ : IrreducibleCharacter G) hsupp
    rw [show ((⟨ψ, hψ⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) = ψ from rfl] at h
    rw [← h, hsum]
  have hcnn : ∀ ψ : ClassFunction G ℂ, ψ ∈ c.support → 0 ≤ c ψ := by
    intro ψ hψsupp
    have hψ : ψ ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr hψsupp)
    have hψirr : IsIrreducibleCharacter ψ := mem_irreducibleCharacters.mp hψ
    have hnn : (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.induce H θ) ψ := by
      rw [ClassFunction.inner_induce_eq_inner_restrict]
      exact inner_isCharacter_nonneg hθ (isCharacter_restrict hψirr.isCharacter H)
    have : (0 : ℂ) ≤ (c ψ : ℂ) := by rw [hcoeff ψ hψ]; exact hnn
    exact_mod_cast this
  refine ⟨Finsupp.mapRange Int.toNat Int.toNat_zero c, ?_, ?_, ?_⟩
  · refine subset_trans ?_ hsupp
    intro ψ hψ
    exact Finset.mem_coe.mpr (Finsupp.support_mapRange (Finset.mem_coe.mp hψ))
  · have hsupp_eq : (Finsupp.mapRange Int.toNat Int.toNat_zero c).support = c.support := by
      apply Finset.Subset.antisymm Finsupp.support_mapRange
      intro a ha
      rw [Finsupp.mem_support_iff, Finsupp.mapRange_apply]
      have : 0 < c a := lt_of_le_of_ne (hcnn a ha) (Ne.symm (Finsupp.mem_support_iff.mp ha))
      omega
    rw [hsum, hsupp_eq]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finsupp.mapRange_apply]
    have : 0 < c a := lt_of_le_of_ne (hcnn a ha) (Ne.symm (Finsupp.mem_support_iff.mp ha))
    rw [← Int.cast_natCast (R := ℂ) (Int.toNat (c a)), Int.toNat_of_nonneg (le_of_lt this)]
  · intro ψ hψ
    rw [Finsupp.mapRange_apply, ← hcoeff ψ hψ]
    have hnn : 0 ≤ c ψ := by
      by_cases hsupp_mem : ψ ∈ c.support
      · exact hcnn ψ hsupp_mem
      · rw [Finsupp.notMem_support_iff.mp hsupp_mem]
    rw [← Int.cast_natCast (R := ℂ) (Int.toNat (c ψ)), Int.toNat_of_nonneg hnn]

set_option linter.unusedFintypeInType false in
/-- The induced character `Ind_H^G θ` of a genuine character is genuine
(cf. `S08.isCharacter_induce`).  Combine `induce_exists_natFinsupp_eq_sum` with its converse
`isCharacter_of_natFinsupp_eq_sum`. -/
theorem isCharacter_induce [Fintype G]
    [Invertible (Nat.card G : ℂ)] {H : Subgroup G} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] {θ : ClassFunction ↥H ℂ} (hθ : IsCharacter θ) :
    IsCharacter (ClassFunction.induce H θ) := by
  obtain ⟨m, hsupp, hsum, _⟩ := induce_exists_natFinsupp_eq_sum hθ
  exact isCharacter_of_natFinsupp_eq_sum m hsupp hsum

/-- **Finset constituent-degree bound.**  If `χ` is a genuine character and `f` is a family,
injective and consisting of irreducible constituents of `χ` (`⟨χ, f i⟩ ≠ 0`) on a finset `s`,
then the sum of the degrees `∑_{i ∈ s} (f i)(1)` is at most `χ(1)` (real parts).  Each `f i` is a
distinct irreducible summand of the `ℕ`-decomposition of `χ` with multiplicity `≥ 1`
(the Finset generalization of `IsCharacter.apply_one_re_le_of_inner_ne_zero`). -/
theorem sum_apply_one_re_le_of_inner_ne_zero [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {χ : ClassFunction G ℂ} (hχ : IsCharacter χ)
    {ι : Type*} {s : Finset ι} {f : ι → ClassFunction G ℂ}
    (hinj : Function.Injective f)
    (hirr : ∀ i ∈ s, IsIrreducibleCharacter (f i))
    (hconst : ∀ i ∈ s, ClassFunction.inner χ (f i) ≠ 0) :
    ∑ i ∈ s, (f i 1).re ≤ (χ 1).re := by
  classical
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := hχ.exists_natFinsupp_eq_sum
  have hsum_apply : ∀ (t : Finset (ClassFunction G ℂ))
      (F : ClassFunction G ℂ → ClassFunction G ℂ),
      (∑ a ∈ t, F a) 1 = ∑ a ∈ t, (F a) 1 := by
    intro t F
    induction t using Finset.cons_induction with
    | empty => simp
    | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, ClassFunction.add_apply, ih]
  have hχ1 : (χ 1).re = ∑ a ∈ m.support, (m a : ℝ) * (a 1).re := by
    have hval : χ 1 = ∑ a ∈ m.support, (m a : ℂ) * (a 1) := by
      rw [hsum, hsum_apply]
      exact Finset.sum_congr rfl fun a _ => ClassFunction.smul_apply _ _ _
    rw [hval, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  have hdeg_nonneg : ∀ a ∈ m.support, (0 : ℝ) ≤ (a 1).re := by
    intro a ha
    have ha_mem : a ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr ha)
    obtain ⟨d, _, hd1⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨a, ha_mem⟩ : IrreducibleCharacter G)
    have hd1' : a (1 : G) = (d : ℂ) := hd1
    rw [hd1', Complex.natCast_re]
    exact Nat.cast_nonneg d
  have hterm_nonneg : ∀ a ∈ m.support, (0 : ℝ) ≤ (m a : ℝ) * (a 1).re := fun a ha =>
    mul_nonneg (Nat.cast_nonneg _) (hdeg_nonneg a ha)
  have hfsupp : ∀ i ∈ s, f i ∈ m.support := by
    intro i hi
    refine Finsupp.mem_support_iff.mpr ?_
    intro h0
    exact hconst i hi (by rw [← hcoeff (f i) (hirr i hi), h0, Nat.cast_zero])
  have himg : Finset.image f s ⊆ m.support := by
    intro a ha; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha; exact hfsupp i hi
  have hsum_img : ∑ i ∈ s, (f i 1).re = ∑ a ∈ Finset.image f s, (a 1).re := by
    rw [Finset.sum_image fun x _ y _ h => hinj h]
  rw [hsum_img, hχ1]
  refine le_trans (Finset.sum_le_sum fun a ha => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg himg fun a ha _ => hterm_nonneg a ha)
  have ha_supp : a ∈ m.support := himg ha
  have hm1 : (1 : ℝ) ≤ (m a : ℝ) :=
    by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp ha_supp)
  exact le_mul_of_one_le_left (hdeg_nonneg a ha_supp) hm1

/-- **Tight constituent-degree bound forces the exact decomposition.**  In addition to the
hypotheses of `sum_apply_one_re_le_of_inner_ne_zero`, if the degree sum dominates `χ(1)`
(`(χ 1).re ≤ ∑_{i ∈ s} (f i)(1)`), then `χ = ∑_{i ∈ s} f i`: the `f i` are *all* the irreducible
constituents of `χ`, each with multiplicity exactly `1`.  (The textbook "a genuine character whose
degree equals the sum of the degrees of distinct constituents is their sum" step.) -/
theorem eq_sum_of_apply_one_re_le_of_inner_ne_zero [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {χ : ClassFunction G ℂ} (hχ : IsCharacter χ)
    {ι : Type*} {s : Finset ι} {f : ι → ClassFunction G ℂ}
    (hinj : Function.Injective f)
    (hirr : ∀ i ∈ s, IsIrreducibleCharacter (f i))
    (hconst : ∀ i ∈ s, ClassFunction.inner χ (f i) ≠ 0)
    (hle : (χ 1).re ≤ ∑ i ∈ s, (f i 1).re) :
    χ = ∑ i ∈ s, f i := by
  classical
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := hχ.exists_natFinsupp_eq_sum
  have hsum_apply : ∀ (t : Finset (ClassFunction G ℂ))
      (F : ClassFunction G ℂ → ClassFunction G ℂ),
      (∑ a ∈ t, F a) 1 = ∑ a ∈ t, (F a) 1 := by
    intro t F
    induction t using Finset.cons_induction with
    | empty => simp
    | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, ClassFunction.add_apply, ih]
  have hχ1 : (χ 1).re = ∑ a ∈ m.support, (m a : ℝ) * (a 1).re := by
    have hval : χ 1 = ∑ a ∈ m.support, (m a : ℂ) * (a 1) := by
      rw [hsum, hsum_apply]
      exact Finset.sum_congr rfl fun a _ => ClassFunction.smul_apply _ _ _
    rw [hval, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  have hdeg_nonneg : ∀ a ∈ m.support, (0 : ℝ) ≤ (a 1).re := by
    intro a ha
    have ha_mem : a ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr ha)
    obtain ⟨d, _, hd1⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨a, ha_mem⟩ : IrreducibleCharacter G)
    have hd1' : a (1 : G) = (d : ℂ) := hd1
    rw [hd1', Complex.natCast_re]
    exact Nat.cast_nonneg d
  have hdeg_pos : ∀ a ∈ m.support, (0 : ℝ) < (a 1).re := by
    intro a ha
    have ha_mem : a ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr ha)
    obtain ⟨d, hd, hd1⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨a, ha_mem⟩ : IrreducibleCharacter G)
    have hd1' : a (1 : G) = (d : ℂ) := hd1
    rw [hd1', Complex.natCast_re]
    exact_mod_cast hd
  have hm_ge1 : ∀ a ∈ m.support, (1 : ℝ) ≤ (m a : ℝ) := fun a ha => by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp ha)
  have hfsupp : ∀ i ∈ s, f i ∈ m.support := by
    intro i hi
    refine Finsupp.mem_support_iff.mpr ?_
    intro h0
    exact hconst i hi (by rw [← hcoeff (f i) (hirr i hi), h0, Nat.cast_zero])
  have himg : Finset.image f s ⊆ m.support := by
    intro a ha; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha; exact hfsupp i hi
  have hsum_img : ∑ i ∈ s, (f i 1).re = ∑ a ∈ Finset.image f s, (a 1).re := by
    rw [Finset.sum_image fun x _ y _ h => hinj h]
  -- key degree equality: `∑_{supp} m_a (a1).re = ∑_{image} (a1).re`
  have hkey : ∑ a ∈ m.support, (m a : ℝ) * (a 1).re
      = ∑ a ∈ Finset.image f s, (a 1).re := by
    have hbound := sum_apply_one_re_le_of_inner_ne_zero hχ hinj hirr hconst
    rw [hsum_img] at hbound hle
    rw [hχ1] at hbound hle
    exact le_antisymm hle hbound
  -- split the support into `image` and `support \ image`
  have hsplit : (∑ a ∈ m.support \ Finset.image f s, (m a : ℝ) * (a 1).re)
      + ∑ a ∈ Finset.image f s, (m a : ℝ) * (a 1).re
      = ∑ a ∈ m.support, (m a : ℝ) * (a 1).re := Finset.sum_sdiff himg
  have himg_ge : ∑ a ∈ Finset.image f s, (a 1).re
      ≤ ∑ a ∈ Finset.image f s, (m a : ℝ) * (a 1).re :=
    Finset.sum_le_sum fun a ha =>
      le_mul_of_one_le_left (hdeg_nonneg a (himg ha)) (hm_ge1 a (himg ha))
  have hsdiff_nonneg : 0 ≤ ∑ a ∈ m.support \ Finset.image f s, (m a : ℝ) * (a 1).re :=
    Finset.sum_nonneg fun a ha =>
      mul_nonneg (Nat.cast_nonneg _) (hdeg_nonneg a (Finset.mem_sdiff.mp ha).1)
  -- `hkey` + `hsplit`: the `support \ image` and the `image` gaps both vanish
  have heq_total : (∑ a ∈ m.support \ Finset.image f s, (m a : ℝ) * (a 1).re)
      + ∑ a ∈ Finset.image f s, (m a : ℝ) * (a 1).re
      = ∑ a ∈ Finset.image f s, (a 1).re := hsplit.trans hkey
  have hsdiff_zero : (∑ a ∈ m.support \ Finset.image f s, (m a : ℝ) * (a 1).re) = 0 := by
    linarith
  have himg_eq : ∑ a ∈ Finset.image f s, (m a : ℝ) * (a 1).re
      = ∑ a ∈ Finset.image f s, (a 1).re := by linarith
  -- the support is exactly the image
  have hsupp_eq : m.support = Finset.image f s := by
    refine Finset.Subset.antisymm ?_ himg
    intro a ha
    by_contra hnot
    have ha_sdiff : a ∈ m.support \ Finset.image f s := Finset.mem_sdiff.mpr ⟨ha, hnot⟩
    have hga0 : (m a : ℝ) * (a 1).re = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun b hb =>
        mul_nonneg (Nat.cast_nonneg _) (hdeg_nonneg b (Finset.mem_sdiff.mp hb).1)).mp
        hsdiff_zero a ha_sdiff
    have hga_pos : 0 < (m a : ℝ) * (a 1).re :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha))
        (hdeg_pos a ha)
    linarith
  -- the multiplicity on the image is exactly `1`
  have hm_one : ∀ a ∈ Finset.image f s, m a = 1 := by
    have hgg : ∀ a ∈ Finset.image f s, (a 1).re = (m a : ℝ) * (a 1).re :=
      (Finset.sum_eq_sum_iff_of_le fun b hb =>
        le_mul_of_one_le_left (hdeg_nonneg b (himg hb)) (hm_ge1 b (himg hb))).mp himg_eq.symm
    intro a ha
    have h1 := hgg a ha
    have hpos := hdeg_pos a (himg ha)
    have : (m a : ℝ) = 1 :=
      mul_right_cancel₀ (ne_of_gt hpos) (by rw [one_mul]; exact h1.symm)
    exact_mod_cast this
  -- assemble
  have hsum_f : ∑ i ∈ s, f i = ∑ a ∈ Finset.image f s, a := by
    rw [Finset.sum_image fun x _ y _ h => hinj h]
  rw [hsum_f, hsum, hsupp_eq]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hm_one a ha, Nat.cast_one, one_smul]

/-- **Singleton case of `eq_sum_of_apply_one_re_le_of_inner_ne_zero`**: a genuine character whose
degree is at most that of one of its irreducible constituents `θ` equals `θ`.  (Together with the
automatic `θ(1) ≤ χ(1)`, this is the equal-degree-constituent uniqueness.) -/
theorem eq_of_apply_one_re_le_of_inner_ne_zero [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {χ θ : ClassFunction G ℂ} (hχ : IsCharacter χ)
    (hθ : IsIrreducibleCharacter θ) (hconst : ClassFunction.inner χ θ ≠ 0)
    (hle : (χ 1).re ≤ (θ 1).re) :
    χ = θ := by
  have h := eq_sum_of_apply_one_re_le_of_inner_ne_zero (ι := Unit) (s := {()})
    (f := fun _ => θ) hχ (fun a b _ => Subsingleton.elim a b)
    (fun _ _ => hθ) (fun _ _ => hconst) (by simpa using hle)
  simpa using h

end CharacterInfra

variable {L : Type*} [Group L] [Fintype L]

namespace Hypothesis

variable (h : Hypothesis L)

omit [Fintype L] in
/-- **`W ⊓ K = W₂` (membership form)** (mmd 04.6, (4.5) proof "`K ∩ W = W₂`"): an element of
`W = W₁ ⊔ W₂` that lies in `K` already lies in `W₂`.  Writing it as `x·y` with `x ∈ W₁`,
`y ∈ W₂ ≤ K`, the `W₁`-part `x = (x·y)·y⁻¹` lies in `K`, hence in `K ⊓ W₁ = ⊥`
(`isComplement.disjoint`), so `x = 1` and the element is `y ∈ W₂`. -/
theorem mem_W2_of_mem_sup_of_mem_K {a : L} (ha : a ∈ h.W1 ⊔ h.W2) (haK : a ∈ h.K) :
    a ∈ h.W2 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_of_mem_sup ha
  have hyK : y ∈ h.K := h.W2_le_K hy
  have hxK : x ∈ h.K := by
    have hx_eq : x = a * y⁻¹ := by rw [← hxy]; group
    rw [hx_eq]
    exact h.K.mul_mem haK (h.K.inv_mem hyK)
  have hx1 : x = 1 := by
    have hmem : x ∈ h.K ⊓ h.W1 := ⟨hxK, hx⟩
    rwa [disjoint_iff.mp h.isComplement.disjoint, Subgroup.mem_bot] at hmem
  rw [← hxy, hx1, one_mul]
  exact hy

omit [Fintype L] in
/-- **Peterfalvi (4.5.b), key fixed-class lemma** (mmd 04.6, (4.5.b) proof): a conjugacy class
`C` of `K` normalized by `g ∈ W₁^#` meets `W₂`.

The cyclic group `⟨φ⟩ ≤ MulAut K`, `φ =` conjugation by `g`, acts on the (`φ`-invariant) class
`C`.  Were `C` disjoint from `W₂`, this action would be free: a fixed point `c` of a nontrivial
power `φⁿ =` conjugation by `gⁿ` (`gⁿ ≠ 1` because `φⁿ ≠ 1`) would lie in `C_K(gⁿ) = W₂`
(`centralizer_W2`, as `gⁿ ∈ W₁^#`).  A free action of a finite group divides the set it acts
on (`card_group_dvd_card_of_freeAction`), so `|⟨φ⟩| = ord φ` divides `|C|`, which divides `|K|`;
but `ord φ ∣ ord g ∣ w₁` and `gcd(|K|, w₁) = 1` force `ord φ = 1`, i.e. `φ = 1`.  Then `g`
centralizes all of `K`, so the representative `a ∈ C` lies in `C_K(g) = W₂` — contradiction. -/
theorem conjClass_meets_W2 [Finite L] (g : L) (hg : g ∈ h.W1) (hg1 : g ≠ 1) (C : ConjClasses ↥h.K)
    (hC : ConjClasses.conjByPerm (G := L) (H := h.K) g C = C) :
    ∃ c : ↥h.K, c ∈ C.carrier ∧ (c : L) ∈ h.W2 := by
  have := h.K_normal
  have : Finite ↥h.K := Fintype.ofFinite _ |>.finite
  classical
  obtain ⟨a, ha⟩ := C.exists_rep
  -- membership in the class ⟺ conjugacy with the representative `a`
  have hmem_iff : ∀ x : ↥h.K, x ∈ C.carrier ↔ IsConj x a := fun x => by
    rw [ConjClasses.mem_carrier_iff_mk_eq, ← ha, ConjClasses.mk_eq_mk_iff_isConj]
  -- automorphisms preserve conjugacy
  have hmapconj : ∀ (ψ : MulAut ↥h.K) {x y : ↥h.K}, IsConj x y → IsConj (ψ x) (ψ y) := by
    intro ψ x y hxy
    simpa only [MulEquiv.coe_toMonoidHom] using ψ.toMonoidHom.map_isConj hxy
  by_contra hno
  push Not at hno
  set φ : MulAut ↥h.K := MulAut.conjNormal g with hφ
  -- `C` is `g`-stable: `IsConj (φ a) a`
  have hconj_a : IsConj (φ a) a := by
    have hh := hC
    rw [← ha, ConjClasses.conjByPerm_mk] at hh
    have heq : ClassFunction.conjByMulEquiv (G := L) (H := h.K) g a = φ a := by
      apply Subtype.ext
      rw [ClassFunction.conjByMulEquiv_apply, hφ, MulAut.conjNormal_apply]
    rw [heq] at hh
    exact ConjClasses.mk_eq_mk_iff_isConj.mp hh
  -- every power of `φ` fixes the conjugacy class of `a`
  have hψa : ∀ ψ ∈ Subgroup.zpowers φ, IsConj (ψ a) a := by
    let S : Subgroup (MulAut ↥h.K) :=
      { carrier := {ψ | IsConj (ψ a) a}
        one_mem' := by simpa only [Set.mem_ofPred_eq, MulAut.one_apply] using IsConj.refl a
        mul_mem' := fun {ψ₁ ψ₂} h₁ h₂ => by
          change IsConj ((ψ₁ * ψ₂) a) a
          rw [MulAut.mul_apply]
          exact (hmapconj ψ₁ h₂).trans h₁
        inv_mem' := fun {ψ} hψ => by
          change IsConj (ψ⁻¹ a) a
          have h3 : IsConj (ψ⁻¹ (ψ a)) (ψ⁻¹ a) := hmapconj ψ⁻¹ hψ
          rw [MulAut.inv_apply_self] at h3
          exact h3.symm }
    exact fun ψ hψ => (Subgroup.zpowers_le.mpr (show φ ∈ S from hconj_a)) hψ
  -- the cyclic group `⟨φ⟩` acts on `C` (its carrier is `φ`-invariant)
  let sma : SubMulAction ↥(Subgroup.zpowers φ) ↥h.K :=
    { carrier := C.carrier
      smul_mem' := fun c {x} hx => by
        rw [hmem_iff] at hx ⊢
        exact ((hmapconj _ hx).trans (hψa _ c.2) : IsConj ((c : MulAut ↥h.K) x) a) }
  have : Finite (MulAut ↥h.K) := inferInstance
  -- free action: under `hno`, no nontrivial power of `φ` fixes a point of `C`
  have hfree : ∀ (s : ↥(Subgroup.zpowers φ)) (y : ↥sma), s • y = y → s = 1 := by
    intro s y hsy
    by_contra hs1
    obtain ⟨n, hn⟩ := (s.2 : (s : MulAut ↥h.K) ∈ Subgroup.zpowers φ)
    have hsval : (s : MulAut ↥h.K) = MulAut.conjNormal (g ^ n) := by
      have hmz := (MulAut.conjNormal (H := h.K)).map_zpow g n
      rw [← hn, hφ, hmz]
    -- `s • y = y` ⟹ `gⁿ` centralizes `↑y`
    have hyval : (MulAut.conjNormal (g ^ n)) (y : ↥h.K) = (y : ↥h.K) := by
      have h2 : (s : MulAut ↥h.K) (y : ↥h.K) = (y : ↥h.K) := Subtype.ext_iff.mp hsy
      rwa [hsval] at h2
    have hgn1 : g ^ n ≠ 1 := fun hgn =>
      hs1 (OneMemClass.coe_eq_one.mp (by rw [hsval, hgn, map_one] : (s : MulAut ↥h.K) = 1))
    have hgnW1 : g ^ n ∈ h.W1 := h.W1.zpow_mem hg n
    have hcomm : (g ^ n) * ((y : ↥h.K) : L) * (g ^ n)⁻¹ = ((y : ↥h.K) : L) := by
      have := congrArg Subtype.val hyval
      rwa [MulAut.conjNormal_apply] at this
    have hyW2 : ((y : ↥h.K) : L) ∈ h.W2 := by
      have hmem_inf : ((y : ↥h.K) : L) ∈ Subgroup.centralizer ({g ^ n} : Set L) ⊓ h.K :=
        Subgroup.mem_inf.mpr ⟨by
          rw [Subgroup.mem_centralizer_iff]
          rintro m hm
          rw [Set.mem_singleton_iff] at hm; subst hm
          exact mul_inv_eq_iff_eq_mul.mp hcomm, (y : ↥h.K).2⟩
      rwa [h.centralizer_W2 (g ^ n) hgnW1 hgn1] at hmem_inf
    exact hno (y : ↥h.K) y.2 hyW2
  -- divisibility chain ⟹ `ord φ = 1` ⟹ `φ = 1`
  have hdvd1 : Nat.card ↥(Subgroup.zpowers φ) ∣ Nat.card ↥sma :=
    card_group_dvd_card_of_freeAction hfree
  have hsma_card : Nat.card ↥sma = Nat.card ↥(C.carrier) := rfl
  have hcar_dvd : Nat.card ↥(C.carrier) ∣ Nat.card ↥h.K := by
    have hcar : (C.carrier : Set ↥h.K) = MulAction.orbit (ConjAct ↥h.K) a := by
      rw [← ha, ← ConjAct.orbit_eq_carrier_conjClasses]
    rw [hcar]
    calc Nat.card ↥(MulAction.orbit (ConjAct ↥h.K) a)
        = Nat.card (ConjAct ↥h.K ⧸ MulAction.stabilizer (ConjAct ↥h.K) a) :=
          Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ a)
      _ = (MulAction.stabilizer (ConjAct ↥h.K) a).index := (Subgroup.index_eq_card _).symm
      _ ∣ Nat.card (ConjAct ↥h.K) := Subgroup.index_dvd_card _
      _ = Nat.card ↥h.K := Nat.card_congr ConjAct.ofConjAct.toEquiv
  have hφdvdK : orderOf φ ∣ Nat.card ↥h.K := by
    rw [← Nat.card_zpowers]; exact (hsma_card ▸ hdvd1).trans hcar_dvd
  have hφdvdW1 : orderOf φ ∣ Nat.card ↥h.W1 := by
    have hφg : orderOf φ ∣ orderOf g := by rw [hφ]; exact orderOf_map_dvd _ g
    exact hφg.trans (Subgroup.orderOf_dvd_natCard _ hg)
  have hφ1 : orderOf φ = 1 := by
    have := Nat.dvd_gcd hφdvdK hφdvdW1
    rwa [h.card_coprime, Nat.dvd_one] at this
  -- `φ = 1`: `g` centralizes `a`, so `a ∈ C_K(g) = W₂` — contradicting `hno`
  have hφeq1 : φ = 1 := orderOf_eq_one_iff.mp hφ1
  have ha_mem : a ∈ C.carrier := (hmem_iff a).mpr (IsConj.refl a)
  have haW2 : (a : L) ∈ h.W2 := by
    have hcomm : g * (a : L) * g⁻¹ = (a : L) := by
      have hval : (φ a : L) = (a : L) := by rw [hφeq1, MulAut.one_apply]
      rw [hφ, MulAut.conjNormal_apply] at hval
      exact hval
    have hmem_inf : (a : L) ∈ Subgroup.centralizer ({g} : Set L) ⊓ h.K :=
      Subgroup.mem_inf.mpr ⟨by
        rw [Subgroup.mem_centralizer_iff]
        rintro m hm
        rw [Set.mem_singleton_iff] at hm; subst hm
        exact mul_inv_eq_iff_eq_mul.mp hcomm, a.2⟩
    rwa [h.centralizer_W2 g hg hg1] at hmem_inf
  exact hno a ha_mem haW2

omit [Fintype L] in
/-- **Peterfalvi (4.5.b), counting bound on `g`-stable classes** (mmd 04.6, (4.5.b) proof):
for `g ∈ W₁^#`, the number of conjugacy classes of `K` normalized by `g` is at most `w₂`.
Each such class meets `W₂` (`conjClass_meets_W2`), and distinct classes are disjoint, so picking
a `W₂`-representative injects the `g`-stable classes into `W₂`. -/
theorem card_fixed_conjClasses_le_W2 [Finite L] (g : L) (hg : g ∈ h.W1) (hg1 : g ≠ 1) :
    Nat.card (Function.fixedPoints (ConjClasses.conjByPerm (G := L) (H := h.K) g))
      ≤ Nat.card ↥h.W2 := by
  have := h.K_normal
  have : Finite ↥h.K := Fintype.ofFinite _ |>.finite
  classical
  -- a `W₂`-representative of each `g`-stable class
  let wit : Function.fixedPoints (ConjClasses.conjByPerm (G := L) (H := h.K) g) → ↥h.K :=
    fun p => (h.conjClass_meets_W2 g hg hg1 p.1 p.2).choose
  have hwit_carrier : ∀ p, wit p ∈ p.1.carrier :=
    fun p => (h.conjClass_meets_W2 g hg hg1 p.1 p.2).choose_spec.1
  have hwit_W2 : ∀ p, ((wit p : L)) ∈ h.W2 :=
    fun p => (h.conjClass_meets_W2 g hg hg1 p.1 p.2).choose_spec.2
  refine Nat.card_le_card_of_injective (fun p => (⟨(wit p : L), hwit_W2 p⟩ : ↥h.W2)) ?_
  intro p q hpq
  have hL := Subtype.ext_iff.mp hpq
  have hwit_eq : wit p = wit q := Subtype.ext hL
  apply Subtype.ext
  calc p.1 = ConjClasses.mk (wit p) := (ConjClasses.mem_carrier_iff_mk_eq.mp (hwit_carrier p)).symm
    _ = ConjClasses.mk (wit q) := by rw [hwit_eq]
    _ = q.1 := ConjClasses.mem_carrier_iff_mk_eq.mp (hwit_carrier q)

omit [Fintype L] in
/-- **Peterfalvi (4.5.b), `g` fixes at most `w₂` irreducibles** (mmd 04.6, (4.5.b) proof, via
[Is] Theorem 6.32): for `g ∈ W₁^#`, conjugation by `g` fixes at most `w₂` irreducible characters
of `K`.  Brauer's permutation lemma equates the count of `g`-fixed irreducibles with the count of
`g`-stable conjugacy classes (`card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`),
which is `≤ w₂` by `card_fixed_conjClasses_le_W2`. -/
theorem card_fixed_irr_le_W2 [Finite L] (g : L) (hg : g ∈ h.W1) (hg1 : g ≠ 1) :
    Nat.card (Function.fixedPoints (IrreducibleCharacter.conjByPerm (G := L) (H := h.K) g))
      ≤ Nat.card ↥h.W2 := by
  have := h.K_normal
  have : Finite ↥h.K := Fintype.ofFinite _ |>.finite
  rw [card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm]
  exact h.card_fixed_conjClasses_le_W2 g hg hg1

section Recipe

variable [Invertible (Nat.card L : ℂ)]
  [Fintype ↥(h.W1 ⊔ h.W2)]
  [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]

omit [Invertible (Nat.card L : ℂ)] in
omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **The induced column difference `Ind_W^L(ω_{ij} − ω_{0j})` vanishes on `K`** (mmd 04.6,
(4.5.a) proof).  The source difference `ω_{ij} − ω_{0j}` is supported on `W − W₂` (the two
linear characters of a column agree on `W₂`, `omega_omegaProdChar_sub_eq_zero_of_mem_W2`), so
the induced class function vanishes off the `L`-conjugates of `W − W₂`.  No conjugate of an
element `k ∈ K` lands there: `K ⊴ L` gives `x⁻¹kx ∈ K`, and if it also lies in `W` then it lies
in `W ⊓ K = W₂` (`mem_W2_of_mem_sup_of_mem_K`), i.e. outside `W − W₂`. -/
theorem induce_chiColumnDiff_eq_zero_of_mem_K [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {k : L} (hk : k ∈ h.K) :
    ClassFunction.induce h.sdiffTICyclicHypothesis.W
      ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) k = 0 := by
  refine ClassFunction.induce_eq_zero_of_not_conjugatesIntoSet
    (A := {w : ↥h.sdiffTICyclicHypothesis.W | (w : L) ∉ h.W2}) ?_ ?_
  · -- the difference is supported on `W − W₂`: it vanishes on `W₂`
    intro w hw
    rw [ClassFunction.mem_support] at hw
    rw [Set.mem_ofPred_eq]
    intro hwmem
    apply hw
    have hwW2 : w ∈ h.W2.subgroupOf h.sdiffTICyclicHypothesis.W := by
      rw [Subgroup.mem_subgroupOf]; exact hwmem
    rw [ClassFunction.sub_apply]
    exact omega_omegaProdChar_sub_eq_zero_of_mem_W2 h.sdiffTICyclicHypothesis
      (h.w1CharEquiv i) (h.w1CharEquiv 0) χ₂ hwW2
  · -- `k` is not conjugate into `W − W₂`
    rintro ⟨x, hx, hxA⟩
    rw [Set.mem_ofPred_eq] at hxA
    apply hxA
    have hconjK : x⁻¹ * k * x ∈ h.K := by
      simpa using h.K_normal.conj_mem k hk x⁻¹
    have hxW : x⁻¹ * k * x ∈ h.W1 ⊔ h.W2 := hx
    exact h.mem_W2_of_mem_sup_of_mem_K hxW hconjK

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.5.a), key vanishing**: the signed difference `μ_{ij} − μ_{0j}` of a column
vanishes on `K`.  It equals `δ_j · Ind_W^L(ω_{ij} − ω_{0j})` (`columnFamily_spec`,
`isometryDifferenceImage_induceZ`), which vanishes on `K`
(`induce_chiColumnDiff_eq_zero_of_mem_K`), and `δ_j = ±1 ≠ 0`. -/
theorem columnFamily_difference_vanishes_on_K [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {k : L} (hk : k ∈ h.K) :
    (h.columnFamily χ₂).difference i k = 0 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have hsd : (h.columnFamily χ₂).signedDifference i k = 0 := by
    rw [← h.columnFamily_spec χ₂ i, isometryDifferenceImage_induceZ]
    exact h.induce_chiColumnDiff_eq_zero_of_mem_K χ₂ i hk
  rw [SignedIrreducibleDifferenceFamily.signedDifference_apply, ClassFunction.zsmul_apply,
    zsmul_eq_mul] at hsd
  have hs : ((h.columnFamily χ₂).sign : ℂ) ≠ 0 := by
    rcases (h.columnFamily χ₂).sign_eq with he | he <;> rw [he] <;> norm_num
  exact (mul_eq_zero.mp hsd).resolve_left hs

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.5.a), independence of `i`**: the restriction `χ_j = Res^L_K μ_{ij}` does
not depend on the `W₁`-index `i`.  Indeed `μ_{ij} − μ_{0j}` vanishes on `K`
(`columnFamily_difference_vanishes_on_K`), so `μ_{ij}` and `μ_{0j}` agree on `K`. -/
theorem restrict_certainType_eq [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.restrict h.K ((h.columnFamily χ₂).mu i : ClassFunction L ℂ)
      = ClassFunction.restrict h.K ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  ext k
  rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply, ← sub_eq_zero]
  have hdiff := h.columnFamily_difference_vanishes_on_K χ₂ i k.2
  rwa [SignedIrreducibleDifferenceFamily.difference_apply, ClassFunction.sub_apply,
    SignedIrreducibleDifferenceFamily.classFunction_apply,
    SignedIrreducibleDifferenceFamily.classFunction_apply] at hdiff

omit [Fintype L] in
omit [Invertible (Nat.card L : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
  [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] in
/-- **`[L : K] = w₁`** (mmd 04.6, (4.5) proof): the index of the normal subgroup `K` equals
`|W₁|`, since `K` is a complement to `W₁` in `L` (`L/K ≅ W₁` via
`isComplement.QuotientMulEquiv`). -/
theorem index_K_eq : h.K.index = Nat.card h.W1 := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr h.isComplement.symm.QuotientMulEquiv.toEquiv

variable [Invertible (Nat.card ↥h.K : ℂ)]

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.5.a), structure of the restriction** (core): there is an irreducible
character `θ` of `K` equal to the restriction `χ_j = Res^L_K μ_{0j}`, with `Ind^L_K θ = ∑_i μ_{ij}`.

Take an irreducible constituent `θ` of `χ_j` (`exists_liesOver`).  Every `μ_{ij}` restricts to
`χ_j` (`restrict_certainType_eq`), hence lies over `θ`, so the `w₁` distinct irreducibles
`μ_{ij}` are all constituents of `Ind_K^L θ`; the constituent-degree bound
(`sum_apply_one_re_le_of_inner_ne_zero`) gives
`w₁·μ_{0j}(1) = ∑_i μ_{ij}(1) ≤ (Ind θ)(1) = w₁·θ(1)`, so `χ_j(1) = μ_{0j}(1) ≤ θ(1)`.  Since `θ`
is a constituent of `χ_j`, the reverse inequality `θ(1) ≤ χ_j(1)` is automatic, so the
equal-degree uniqueness (`eq_of_apply_one_re_le_of_inner_ne_zero`) forces `χ_j = θ`.  The degree
inequality is then an equality, so the same tight bound (`eq_sum_of_apply_one_re_le…`) identifies
`Ind θ` as exactly `∑_i μ_{ij}`. -/
theorem exists_irreducible_restrict_certainType [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ∃ θ : IrreducibleCharacter ↥h.K,
      ClassFunction.restrict h.K ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)
          = (θ : ClassFunction ↥h.K ℂ) ∧
      ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)
          = ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction L ℂ) := by
  classical
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have : Fintype ↥h.K := Fintype.ofFinite _
  -- `χ_j = Res^L_K μ_{0j}` is a genuine character
  have hχj_char : IsCharacter
      (ClassFunction.restrict h.K ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)) :=
    isCharacter_restrict ((h.columnFamily χ₂).mu 0).isIrreducible.isCharacter h.K
  -- a constituent `θ` of `χ_j`
  obtain ⟨θ, hθ0⟩ :=
    IrreducibleCharacter.exists_liesOver (H := h.K) ((h.columnFamily χ₂).mu 0)
  have hθ_const : ClassFunction.inner
      (ClassFunction.restrict h.K ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ))
      (θ : ClassFunction ↥h.K ℂ) ≠ 0 := hθ0
  -- every `μ_{ij}` is a constituent of `Ind θ` (restrictions agree)
  have hθi : ∀ i, ClassFunction.inner
      (ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ))
      ((h.columnFamily χ₂).classFunction i) ≠ 0 := by
    intro i
    rw [SignedIrreducibleDifferenceFamily.classFunction_apply]
    refine (IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver
      h.K ((h.columnFamily χ₂).mu i) θ).mpr ?_
    rw [IrreducibleCharacter.liesOver_iff, ClassFunction.restrictionMultiplicity_def,
      h.restrict_certainType_eq χ₂ i]
    exact hθ0
  -- `Ind θ` is genuine
  have hIndθ_char : IsCharacter (ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)) :=
    isCharacter_induce θ.isIrreducible.isCharacter
  -- degree bookkeeping: all `μ_{ij}` have the same value at `1`
  have hμi1 : ∀ i, ((h.columnFamily χ₂).mu i : ClassFunction L ℂ) 1
      = ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) 1 := by
    intro i
    have hrw := congrArg (fun (φ : ClassFunction ↥h.K ℂ) => φ (1 : ↥h.K))
      (h.restrict_certainType_eq χ₂ i)
    simpa only [ClassFunction.restrict_apply, OneMemClass.coe_one] using hrw
  -- LHS of the bound: `∑_i μ_{ij}(1) = w₁·μ_{0j}(1)`
  have hsumμ : (∑ i, ((h.columnFamily χ₂).classFunction i 1).re)
      = (Nat.card h.W1 : ℝ) * (((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) 1).re := by
    have hterm : ∀ i : Fin (Nat.card h.W1),
        ((h.columnFamily χ₂).classFunction i 1).re
        = (((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) 1).re := by
      intro i
      rw [SignedIrreducibleDifferenceFamily.classFunction_apply]
      exact congrArg Complex.re (hμi1 i)
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  -- RHS of the bound: `(Ind θ)(1) = w₁·θ(1)`
  have hIndθ1 : ((ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)) 1).re
      = (Nat.card h.W1 : ℝ) * ((θ : ClassFunction ↥h.K ℂ) 1).re := by
    rw [ClassFunction.induce_apply_one, h.index_K_eq, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero]
  -- assemble the degree inequality and cancel `w₁`
  have hbound := sum_apply_one_re_le_of_inner_ne_zero (s := Finset.univ) hIndθ_char
    (h.columnFamily χ₂).classFunction_injective
    (fun i _ => (h.columnFamily χ₂).classFunction_irreducible i) (fun i _ => hθi i)
  rw [hsumμ, hIndθ1] at hbound
  have hw1pos : (0 : ℝ) < (Nat.card h.W1 : ℝ) := by
    have h1 := h.one_lt_card_W1
    have : 0 < Nat.card h.W1 := by omega
    exact_mod_cast this
  have hle : ((ClassFunction.restrict h.K
        ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)) 1).re
      ≤ ((θ : ClassFunction ↥h.K ℂ) 1).re := by
    rw [ClassFunction.restrict_apply, OneMemClass.coe_one]
    exact le_of_mul_le_mul_left hbound hw1pos
  -- equal-degree-with-constituent uniqueness: `χ_j = θ`
  have hχj_eq : ClassFunction.restrict h.K ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)
      = (θ : ClassFunction ↥h.K ℂ) :=
    eq_of_apply_one_re_le_of_inner_ne_zero hχj_char θ.isIrreducible hθ_const hle
  refine ⟨θ, hχj_eq, ?_⟩
  -- `μ_{0j}(1) = θ(1)` (from `χ_j = θ`), so the degree bound is tight on `Ind θ`
  have hdeg_eq : ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) 1
      = (θ : ClassFunction ↥h.K ℂ) 1 := by
    have hrw := congrArg (fun (φ : ClassFunction ↥h.K ℂ) => φ (1 : ↥h.K)) hχj_eq
    simpa only [ClassFunction.restrict_apply, OneMemClass.coe_one] using hrw
  have hle2 : ((ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)) 1).re
      ≤ ∑ i, ((h.columnFamily χ₂).classFunction i 1).re :=
    le_of_eq (by rw [hIndθ1, hsumμ, hdeg_eq])
  -- tight bound ⟹ `Ind θ = ∑_i μ_{ij}`
  have hIndeq : ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)
      = ∑ i, (h.columnFamily χ₂).classFunction i :=
    eq_sum_of_apply_one_re_le_of_inner_ne_zero (s := Finset.univ) hIndθ_char
      (h.columnFamily χ₂).classFunction_injective
      (fun i _ => (h.columnFamily χ₂).classFunction_irreducible i) (fun i _ => hθi i) hle2
  rw [hIndeq]

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.5.a), irreducibility of the restriction**: `χ_j = Res^L_K μ_{0j}` is an
irreducible character of `K` (the first half of `exists_irreducible_restrict_certainType`). -/
theorem certainTypeRestrict_isIrreducible [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    IsIrreducibleCharacter
      (ClassFunction.restrict h.K ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)) := by
  obtain ⟨θ, hχj_eq, _⟩ := h.exists_irreducible_restrict_certainType χ₂
  rw [hχj_eq]
  exact θ.isIrreducible

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.5.a), `Ind^L_K χ_j = μ_j`**: the induction of the (irreducible) restriction
`χ_j = Res^L_K μ_{0j}` is the column sum `μ_j = ∑_i μ_{ij}` (the second half of
`exists_irreducible_restrict_certainType`, with `χ_j = θ`). -/
theorem induce_restrict_certainType_eq [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ClassFunction.induce h.K
        (ClassFunction.restrict h.K ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ))
      = ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction L ℂ) := by
  obtain ⟨θ, hχj_eq, hind⟩ := h.exists_irreducible_restrict_certainType χ₂
  rw [hχj_eq]
  exact hind

omit [Fintype L] in
omit [Invertible (Nat.card L : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
  [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] [Invertible (Nat.card ↥h.K : ℂ)] in
/-- **Bridge: inertia ↔ conjugation-permutation fixed point.**  For `g : L` and `θ ∈ Irr(K)`, `g`
lies in the inertia group of `θ` iff `θ` is fixed by the conjugation permutation
`IrreducibleCharacter.conjByPerm g` (whose fixed-point count is bounded by
`card_fixed_irr_le_W2`). -/
theorem mem_inertia_iff_isFixedPt_conjByPerm (g : L) (θ : IrreducibleCharacter ↥h.K) :
    g ∈ IrreducibleCharacter.inertia (G := L) (H := h.K) θ ↔
      Function.IsFixedPt (IrreducibleCharacter.conjByPerm (G := L) (H := h.K) g) θ := by
  have := h.K_normal
  rw [IrreducibleCharacter.mem_inertia]
  exact Iff.rfl

/-- **`χ_j` packaged as an irreducible character of `K`** (`certainTypeRestrict_isIrreducible`).
Indexed by the `W₂`-column `χ₂ ∈ Ŵ₂`; there are `w₂` of them. -/
noncomputable def chiRestrict [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    IrreducibleCharacter ↥h.K :=
  ⟨ClassFunction.restrict h.K ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ),
   h.certainTypeRestrict_isIrreducible χ₂⟩

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
@[simp] theorem coe_chiRestrict [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ)
      = ClassFunction.restrict h.K ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) :=
  rfl

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **`χ_j` is fixed by every `g ∈ L`** (in particular `g ∈ W₁^#`): it is the restriction of the
`L`-character `μ_{0j}`, so conjugation by any `g ∈ L` fixes it (`conjBy_restrict`). -/
theorem chiRestrict_isFixedPt [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (g : L) :
    Function.IsFixedPt (IrreducibleCharacter.conjByPerm (G := L) (H := h.K) g)
      (h.chiRestrict χ₂) := by
  have := h.K_normal
  apply IrreducibleCharacter.ext
  simp only [IrreducibleCharacter.conjByPerm_apply, IrreducibleCharacter.coe_conjBy,
    coe_chiRestrict]
  exact ClassFunction.conjBy_restrict g ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **The `χ_j` are distinct** (injective in the column `χ₂`): if `χ_j = χ_{j'}` then their
inductions `μ_j = ∑_i μ_{ij}` and `μ_{j'} = ∑_i μ_{ij'}` coincide
(`induce_restrict_certainType_eq`),
but `⟨μ_j, μ_{0j}⟩ = 1` while `⟨μ_{j'}, μ_{0j}⟩ = 0` for `j ≠ j'` (cross-column orthogonality
`columnFamily_mu_ne`), a contradiction. -/
theorem chiRestrict_injective [NeZero (Nat.card h.W1)] :
    Function.Injective h.chiRestrict := by
  classical
  intro χ₂ χ₂' heq
  by_contra hne
  -- the column sums coincide
  have hind : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction L ℂ))
      = ∑ i, ((h.columnFamily χ₂').mu i : ClassFunction L ℂ) := by
    have hcoe := congrArg (ClassFunction.induce h.K)
      (congrArg IrreducibleCharacter.toClassFunction heq)
    rwa [coe_chiRestrict, coe_chiRestrict, h.induce_restrict_certainType_eq χ₂,
      h.induce_restrict_certainType_eq χ₂'] at hcoe
  -- inner with `μ_{0j}`: `1` on the left, `0` on the right
  have key : ClassFunction.inner (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction L ℂ))
        ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)
      = ClassFunction.inner (∑ i, ((h.columnFamily χ₂').mu i : ClassFunction L ℂ))
        ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) := by rw [hind]
  rw [inner_sum_left, inner_sum_left] at key
  have hLHS : (∑ i, ClassFunction.inner ((h.columnFamily χ₂).mu i : ClassFunction L ℂ)
      ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)) = 1 := by
    rw [Finset.sum_congr rfl (fun i _ => irreducibleCharacter_inner_eq_ite _ _)]
    rw [Finset.sum_congr rfl (fun i _ => if_congr (h.columnFamily χ₂).injective.eq_iff rfl rfl),
      Finset.sum_ite_eq' Finset.univ (0 : Fin (Nat.card h.W1)) (fun _ => (1 : ℂ)),
      if_pos (Finset.mem_univ _)]
  have hRHS : (∑ i, ClassFunction.inner ((h.columnFamily χ₂').mu i : ClassFunction L ℂ)
      ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [irreducibleCharacter_inner_eq_ite, if_neg (h.columnFamily_mu_ne (Ne.symm hne) i 0)]
  rw [hLHS, hRHS] at key
  exact one_ne_zero key

omit [Invertible (Nat.card L : ℂ)] in
omit [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
  [Invertible (Nat.card ↥h.K : ℂ)] in
omit [Fintype L] in
/-- **The number of columns is `w₂`** (`|Ŵ₂| = |W₂|`, Pontryagin self-duality
`card_charGroup_subgroupOf`).  Together with `chiRestrict_injective` this gives `w₂` distinct
`χ_j ∈ Irr(K)`, matching the `card_fixed_irr_le_W2` bound. -/
theorem card_charGroup_W2 [Finite L] :
    Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = Nat.card h.W2 := by
  have : Fintype L := Fintype.ofFinite L
  exact h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf h.sdiffTICyclicHypothesis.W2_le_W

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Counting collapse** (mmd 04.6, (4.5.b) proof): for `g ∈ W₁^#`, every `g`-fixed irreducible
character of `K` is one of the `χ_j`.  The `w₂` distinct `χ_j` (`chiRestrict_injective`,
`card_charGroup_W2`) all lie in the `g`-fixed set (`chiRestrict_isFixedPt`), whose size is at most
`w₂` (`card_fixed_irr_le_W2`); equality forces the injection `Ŵ₂ ↪ Fix(g)` to be onto. -/
theorem exists_eq_chiRestrict_of_isFixedPt [NeZero (Nat.card h.W1)]
    (g : L) (hg : g ∈ h.W1) (hg1 : g ≠ 1) {χ : IrreducibleCharacter ↥h.K}
    (hfix : Function.IsFixedPt (IrreducibleCharacter.conjByPerm (G := L) (H := h.K) g) χ) :
    ∃ χ₂, h.chiRestrict χ₂ = χ := by
  have := h.K_normal
  have : Finite ↥h.K := Fintype.ofFinite _ |>.finite
  classical
  -- `F : Ŵ₂ → Fix(g)`, `χ₂ ↦ χ_j`, is injective into the `g`-fixed set
  let F : ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) →
      Function.fixedPoints (IrreducibleCharacter.conjByPerm (G := L) (H := h.K) g) :=
    fun χ₂ => ⟨h.chiRestrict χ₂, h.chiRestrict_isFixedPt χ₂ g⟩
  have hFinj : Function.Injective F :=
    fun a b hab => h.chiRestrict_injective (Subtype.ext_iff.mp hab)
  -- cardinality sandwich: `w₂ = |Ŵ₂| ≤ |Fix(g)| ≤ w₂`
  have hle1 : Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
      ≤ Nat.card (Function.fixedPoints (IrreducibleCharacter.conjByPerm (G := L) (H := h.K) g)) :=
    Nat.card_le_card_of_injective F hFinj
  have hle2 := h.card_fixed_irr_le_W2 g hg hg1
  have hcardeq : Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
      = Nat.card (Function.fixedPoints (IrreducibleCharacter.conjByPerm (G := L) (H := h.K) g)) :=
    le_antisymm hle1 (hle2.trans (le_of_eq h.card_charGroup_W2.symm))
  -- injective + equal finite cardinality ⟹ bijective ⟹ surjective
  have : Fintype ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype (Function.fixedPoints
      (IrreducibleCharacter.conjByPerm (G := L) (H := h.K) g)) := Fintype.ofFinite _
  have hbij : Function.Bijective F := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hFinj, by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcardeq⟩
  obtain ⟨χ₂, hχ₂⟩ := hbij.surjective ⟨χ, hfix⟩
  exact ⟨χ₂, Subtype.ext_iff.mp hχ₂⟩

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **The reducible-inducing column `chiRestrict χ₂` is `L`-invariant** (issue 1012, W₁-stability
for
(9.9.b)): `chiRestrict χ₂ = Res_K μ` is the restriction of the `L`-character
`μ = (columnFamily χ₂).mu 0`
(`coe_chiRestrict`), so conjugation by any `g ∈ L` fixes it (`μ` is a class function of `L`,
invariant
under `L`-conjugation). This `L`-inertia-stability is the source↔image bijection input of the
(9.9.b)
reducible count: `induce` is injective on the reducible-inducing columns
(`induce_injective_of_inertia_stable`), since each is fixed by all of `L`. -/
theorem chiRestrict_conjBy_eq [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (g : L) :
    IrreducibleCharacter.conjBy g (h.chiRestrict χ₂) = h.chiRestrict χ₂ := by
  have := h.K_normal
  apply IrreducibleCharacter.ext
  ext x
  rw [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply, coe_chiRestrict,
    ClassFunction.restrict_apply, ClassFunction.restrict_apply]
  exact ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ).conj_eq (x : L) g

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **`induce` is injective on the reducible-inducing columns** (issue 1012, (9.9.b) source↔image):
distinct `W₂`-duals `χ₂` give distinct induced characters `Ind_K^L(chiRestrict χ₂)`.  Each column is
`L`-inertia-stable (`chiRestrict_conjBy_eq`), so `induce_injective_of_inertia_stable` forces
`chiRestrict χ₂ = chiRestrict χ₂'`, hence `χ₂ = χ₂'` (`chiRestrict_injective`).  This makes the
count
of *reducible induced images* equal the count of columns (`= w₂ − 1`), the bridge from the §6 source
count to the §9 family `{φ ∈ 𝒮(H₀) | ¬ irr φ}`. -/
theorem induce_chiRestrict_injective [NeZero (Nat.card h.W1)] [Finite ↥h.K] :
    Function.Injective (fun χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ =>
      ClassFunction.induce h.K (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ)) := by
  have : Fintype ↥h.K := Fintype.ofFinite _
  intro χ₂ χ₂' heq
  exact (h.chiRestrict_injective
    (induce_injective_of_inertia_stable (h.chiRestrict_conjBy_eq χ₂) heq)).symm

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.5.b), inertia computation**: a `χ ∈ Irr(K)` that is none of the `χ_j` has full
inertia group `I_L(χ) = K`.  Write `ℓ ∈ I_L(χ)` as `ℓ = k·w` (`k ∈ K`, `w ∈ W₁`) via the complement
`L = K ⋊ W₁`; then `w = k⁻¹ℓ ∈ I_L(χ)`.  If `w ≠ 1` then `w ∈ W₁^#` fixes `χ`
(`mem_inertia_iff_isFixedPt_conjByPerm`), so `χ` is one of the `χ_j`
(`exists_eq_chiRestrict_of_isFixedPt`) — a contradiction; hence `w = 1` and `ℓ = k ∈ K`. -/
theorem inertia_eq_K_of_forall_chiRestrict_ne [NeZero (Nat.card h.W1)]
    {χ : IrreducibleCharacter ↥h.K} (hχ : ∀ χ₂, h.chiRestrict χ₂ ≠ χ) :
    IrreducibleCharacter.inertia (G := L) (H := h.K) χ = h.K := by
  have := h.K_normal
  refine le_antisymm ?_ (IrreducibleCharacter.subgroup_le_inertia χ)
  intro ℓ hℓ
  obtain ⟨⟨⟨kk, hk⟩, ⟨u, hu⟩⟩, hku, -⟩ := Subgroup.IsComplement.existsUnique h.isComplement ℓ
  change kk * u = ℓ at hku
  have hkI : kk ∈ IrreducibleCharacter.inertia (G := L) (H := h.K) χ :=
    IrreducibleCharacter.subgroup_le_inertia χ hk
  have huI : u ∈ IrreducibleCharacter.inertia (G := L) (H := h.K) χ := by
    have hueq : u = kk⁻¹ * ℓ := by rw [← hku]; group
    rw [hueq]; exact mul_mem (inv_mem hkI) hℓ
  rcases eq_or_ne u 1 with hu1 | hu1
  · rw [← hku, hu1, mul_one]; exact hk
  · exact absurd
      (h.exists_eq_chiRestrict_of_isFixedPt u hu hu1
        ((h.mem_inertia_iff_isFixedPt_conjByPerm u χ).mp huI))
      (not_exists.mpr hχ)

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.5.b), first sentence**: for `χ ∈ Irr(K)` not among the `χ_j`, the induced
character `Ind^L_K χ` is irreducible.  Immediate from `I_L(χ) = K`
(`inertia_eq_K_of_forall_chiRestrict_ne`) and [Is] Theorem 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`). -/
theorem induce_isIrreducible_of_forall_chiRestrict_ne [NeZero (Nat.card h.W1)]
    {χ : IrreducibleCharacter ↥h.K} (hχ : ∀ χ₂, h.chiRestrict χ₂ ≠ χ) :
    IsIrreducibleCharacter (ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ)) := by
  have := h.K_normal
  have : Fintype ↥h.K := Fintype.ofFinite _
  exact isIrreducibleCharacter_induce_of_inertia_eq χ
    (h.inertia_eq_K_of_forall_chiRestrict_ne hχ)

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.5.b), the `μ_j` are reducible**: `Ind^L_K χ_j = μ_j = ∑_i μ_{ij}` is *not*
irreducible.  It equals the sum of the `w₁ ≥ 2` distinct irreducibles `μ_{ij}`
(`induce_restrict_certainType_eq`, `columnFamily.injective`, `one_lt_card_W1`); an irreducible
character meeting two distinct constituents `μ_{0j}, μ_{1j}` with multiplicity `1` would have to
equal both, contradicting their distinctness. -/
theorem induce_chiRestrict_not_isIrreducible [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ¬ IsIrreducibleCharacter
      (ClassFunction.induce h.K (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ)) := by
  classical
  have := h.K_normal
  have : Fintype ↥h.K := Fintype.ofFinite _
  intro hirr
  -- `Ind^L_K χ_j = ∑_i μ_{ij}`
  have hsum : ClassFunction.induce h.K (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ)
      = ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction L ℂ) := by
    rw [coe_chiRestrict, h.induce_restrict_certainType_eq χ₂]
  -- `⟨Ind, μ_{kj}⟩ = 1` for every column index `k`
  have hinner : ∀ k : Fin (Nat.card h.W1),
      ClassFunction.inner ((⟨_, hirr⟩ : IrreducibleCharacter L) : ClassFunction L ℂ)
        ((h.columnFamily χ₂).mu k : ClassFunction L ℂ) = 1 := by
    intro k
    rw [IrreducibleCharacter.coe_mk, hsum, inner_sum_left,
      Finset.sum_congr rfl (fun i _ => irreducibleCharacter_inner_eq_ite _ _),
      Finset.sum_congr rfl (fun i _ => if_congr (h.columnFamily χ₂).injective.eq_iff rfl rfl),
      Finset.sum_ite_eq' Finset.univ k (fun _ => (1 : ℂ)), if_pos (Finset.mem_univ _)]
  -- the irreducible would then equal both `μ_{0j}` and `μ_{1j}`
  have h1 : (1 : ℕ) < Nat.card h.W1 := h.one_lt_card_W1
  have heq : ∀ k : Fin (Nat.card h.W1),
      (⟨_, hirr⟩ : IrreducibleCharacter L) = (h.columnFamily χ₂).mu k := by
    intro k
    by_contra hne
    have hk := hinner k
    rw [irreducibleCharacter_inner_eq_ite, if_neg hne] at hk
    exact one_ne_zero hk.symm
  have hcontra := (h.columnFamily χ₂).injective
    ((heq ⟨0, by omega⟩).symm.trans (heq ⟨1, h1⟩))
  simp [Fin.ext_iff] at hcontra

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.5.b), reducibility criterion**: for `χ ∈ Irr(K)`, the induced character
`Ind^L_K χ` is reducible iff `χ` is one of the `χ_j`.  Forward is the contrapositive of
`induce_isIrreducible_of_forall_chiRestrict_ne`; the reverse is
`induce_chiRestrict_not_isIrreducible`. -/
theorem induce_not_isIrreducible_iff [NeZero (Nat.card h.W1)]
    (χ : IrreducibleCharacter ↥h.K) :
    ¬ IsIrreducibleCharacter (ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ))
      ↔ ∃ χ₂, h.chiRestrict χ₂ = χ := by
  constructor
  · intro hred
    by_contra hcon
    push Not at hcon
    exact hred (h.induce_isIrreducible_of_forall_chiRestrict_ne hcon)
  · rintro ⟨χ₂, rfl⟩
    exact h.induce_chiRestrict_not_isIrreducible χ₂

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
/-- **Peterfalvi (4.5.b), reducible-induction count**: exactly `w₂ = |W₂|` of the irreducible
characters `χ ∈ Irr(K)` induce a *reducible* character of `L` — namely the `w₂` distinct `χ_j`.
This is the count behind Peterfalvi (9.9.b)/(9.8.b): under the (8.4.d) realization of `𝒮(H₀)` as
the `M/H₀`-induction family, the reducible members are the `μ_j`, of which there are
`w₂ − 1 = p − 1` after removing the `H̄`-trivial column `j = 0`. -/
theorem card_reducible_induce_eq_W2 [NeZero (Nat.card h.W1)] :
    Nat.card {χ : IrreducibleCharacter ↥h.K //
        ¬ IsIrreducibleCharacter (ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ))}
      = Nat.card h.W2 := by
  rw [← h.card_charGroup_W2]
  symm
  apply Nat.card_congr
  apply Equiv.ofBijective
    (fun χ₂ => ⟨h.chiRestrict χ₂, h.induce_chiRestrict_not_isIrreducible χ₂⟩)
  refine ⟨fun a b hab => h.chiRestrict_injective (Subtype.ext_iff.mp hab), ?_⟩
  rintro ⟨χ, hχ⟩
  obtain ⟨χ₂, hχ₂⟩ := (h.induce_not_isIrreducible_iff χ).mp hχ
  exact ⟨χ₂, Subtype.ext hχ₂⟩

omit [Fintype ↥(h.W1 ⊔ h.W2)] in
set_option linter.unusedFintypeInType false in
/-- **`induce` is injective on the reducible-inducing irreducibles** (issue 1012, (9.9.b)
source↔image, general form): if `χ, χ' ∈ Irr(K)` both induce *reducible* characters of `L` and
`Ind_K^L χ = Ind_K^L χ'`, then `χ = χ'`.  Every reducible-inducing `χ` is a column `chiRestrict χ₂`
(`induce_not_isIrreducible_iff`), and `induce ∘ chiRestrict` is injective
(`induce_chiRestrict_injective`).  This is the form the §9↔§6 bijection's injectivity uses: the §9
family member `induceHU (inflate χ̄)` determines `χ̄` among the reducible columns, so distinct
reducible `χ̄ ∈ Irr(K̄)` give distinct `𝒮(H₀)`-members. -/
theorem induce_injective_on_reducible [NeZero (Nat.card h.W1)] [Fintype ↥h.K]
    {χ χ' : IrreducibleCharacter ↥h.K}
    (hred : ¬ IsIrreducibleCharacter (ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ)))
    (heq : ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ)
      = ClassFunction.induce h.K (χ' : ClassFunction ↥h.K ℂ)) :
    χ = χ' := by
  obtain ⟨χ₂, rfl⟩ := (h.induce_not_isIrreducible_iff χ).mp hred
  have hred' : ¬ IsIrreducibleCharacter
      (ClassFunction.induce h.K (χ' : ClassFunction ↥h.K ℂ)) := heq ▸ hred
  obtain ⟨χ₂', rfl⟩ := (h.induce_not_isIrreducible_iff χ').mp hred'
  exact congrArg h.chiRestrict (h.induce_chiRestrict_injective heq)

end Recipe

end Hypothesis

end OddOrder.Peterfalvi.S06


