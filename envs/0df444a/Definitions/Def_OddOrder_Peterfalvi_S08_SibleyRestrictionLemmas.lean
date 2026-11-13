-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_SibleyRestrictionLemmas
-- name    : OddOrder_Peterfalvi_S08_SibleyRestrictionLemmas
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:43:03.026288+00:00
-- url     : https://prove2.me/theorems/9856319d-aa63-4a80-a496-a36d8b62b788
-- title:
--   Peterfalvi §8: Sibley–Dade restriction/extension, opening layer
-- statement:
--   The opening layer of the Sibley–Dade restriction/extension argument in Peterfalvi §8, (6.8.1).
--
--   Main results: `coeff_eq_neg_or_edge_of_frobenius` (the (6.8.1) step-4 dichotomy: $b\equiv c\equiv 0\pmod a$ implies $b=0$ or the $m=2$ edge case) and its case-(A)/c2 mirror `coeff_eq_neg_or_edge_c2_caseA`.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_SibleyRestrictionLemmas.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_SibleyRestrictionLemmas.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_XBlockCounting

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.8.1) `a ∣ c`**, case (A) / c2 mirror of `dvd_inner_restrict_extension_Yset_of_frobenius`.
`X`-irreducibility uses `isIrreducibleCharacter_of_mem_Xset_c2_caseA`, and the value/congruence
inputs use the case-(A) `restrict_extension_Yset_degree_value_eq_c2_caseA` /
`restrict_extension_Yset_charValue_cong_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem dvd_inner_restrict_extension_Yset_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cc : ℤ,
      ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁ = (cc : ℂ)
        ∧ (a : ℤ) ∣ cc := by
  classical
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  -- `c := ⟨R, χ₁⟩` is an integer (`R ∈ ZIrr L`, `χ₁` irreducible).
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : R ∈ ZIrr (↥L) := OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁
  obtain ⟨cc, hcc⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = χ₁ from rfl] at hcc
  refine ⟨cc, hcc, ?_⟩
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hane : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
  have hHne : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- pick `z ∈ Zc^#`.
  obtain ⟨⟨z, hz⟩, hzne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (hyp.centralCommutator_ne_bot hHnonab)
  have hz1 : z ≠ 1 := fun h => hzne (Subtype.ext h)
  -- value identity: `χ₁(1)·(R z − R 1) = −c·|L|`, with `χ₁(1) = a|W₁|`, `c = cc`, `|L| = |H||W₁|`.
  have hval := hyp.restrict_extension_Yset_degree_value_eq_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ hz hz1
  rw [← hRdef, hcc, ha] at hval
  have hLcard : (Nat.card ↥L : ℂ) = (Nat.card ↥H : ℂ) * (Nat.card hyp.W1 : ℂ) := by
    have h := Subgroup.index_mul_card H
    rw [hyp.index_H_eq_card_W1] at h
    have hc : ((Nat.card hyp.W1 * Nat.card ↥H : ℕ) : ℂ) = (Nat.card ↥L : ℂ) := by rw [h]
    push_cast at hc; linear_combination -hc
  rw [hLcard] at hval
  -- cancel `|W₁|`: `a·(R z − R 1) = −c·|H|`.
  have haD : (a : ℂ) * (R z - R 1) = -(cc : ℂ) * (Nat.card ↥H : ℂ) := by
    apply mul_left_cancel₀ hW1ne
    linear_combination hval
  -- the (6.7)-congruence: `(R z − R 1)/|H|` is an algebraic integer.
  have hcong := hyp.restrict_extension_Yset_charValue_cong_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hz hz1
  rw [← hRdef, OddOrder.AlgInt.cong_def, Int.cast_natCast] at hcong
  -- `c/a = −((R z − R 1)/|H|)`, so `c/a` is an algebraic integer.
  have hccdiv : (cc : ℂ) / (a : ℂ) = -((R z - R 1) / (Nat.card ↥H : ℂ)) := by
    rw [← neg_div, div_eq_div_iff hane hHne]
    linear_combination haD
  have hintc : IsIntegral ℤ ((cc : ℂ) / (a : ℂ)) := by rw [hccdiv]; exact hcong.neg
  -- a rational algebraic integer is an integer ⟹ `a ∣ c`.
  have hqcast : (((cc : ℚ) / (a : ℚ) : ℚ) : ℂ) = (cc : ℂ) / (a : ℂ) := by push_cast; ring
  obtain ⟨n, hn⟩ := OddOrder.RepresentationTheory.isIntegral_rat_imp_int
    (q := (cc : ℚ) / (a : ℚ)) (by rw [hqcast]; exact hintc)
  rw [hqcast, div_eq_iff hane] at hn
  refine ⟨n, ?_⟩
  have : (cc : ℂ) = ((a : ℤ) * n : ℤ) := by rw [hn]; push_cast; ring
  exact_mod_cast this

/-- **(6.8.1) `a ∣ b`** (mmd 04.8 L176, the `b ≡ 0 (mod a)` half of "`b ≡ c ≡ 0 (mod a)`").  For
`η = η₁ ∈ Y` and an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|` (`a > 0`), the
`η₁^{τ₁}`-coefficient
of the cross-diagonal image `(χ₁−aη₁)^τ` — namely `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩`, which is `b − a` in the
Peterfalvi decomposition (168) `(χ₁−aη₁)^τ = X − aη₁^{τ₁} + b∑η_j^{τ₁}` — is an **integer divisible
by `a`**.  Since `a ∣ (b − a) ⟺ a ∣ b`, this is exactly Peterfalvi's `b ≡ 0 (mod a)`.

Direct route via Dade reciprocity (no need for the full (168) decomposition): `χ₁−aη₁` is supported
on `H^#` (`sMember_scaledDiffSupport_of_charValue_eq`, `χ₁(1) = a·η₁(1)` from `Yset_apply_one`), so
`⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, Res^G_L(η₁^{τ₁})⟩` (`inner_tau_eq_inner_restrict`)
`= ⟨χ₁, R⟩ − a·⟨η₁, R⟩ = c − a·e` (`R = Res^G_L(η₁^{τ₁})`; conjugate symmetry `inner_conj_symm` +
reality of the integers `c = ⟨R,χ₁⟩`, `e = ⟨R,η₁⟩`, `mem_ZIrr_inner_int`).  Since `a ∣ c`
(`dvd_inner_restrict_extension_Yset_of_frobenius`, step 2) and `a ∣ a·e`, `a ∣ (c − a·e)`. -/
theorem dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ bb : ℤ,
      ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.coherentYset.extension η) = (bb : ℂ)
        ∧ (a : ℤ) ∣ bb := by
  classical
  -- step 2: `c = ⟨R, χ₁⟩` is an integer with `a ∣ c`.
  obtain ⟨cc, hcc, hacc⟩ :=
    hyp.dvd_inner_restrict_extension_Yset_of_frobenius hF hHnonab hp hp3 hHp hη hχ₁ ha_pos ha
  -- `R ∈ ZIrr L`, `η₁` irreducible ⟹ `e := ⟨R, η₁⟩ ∈ ℤ`.
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : ClassFunction.restrict L (hyp.coherentYset.extension η) ∈ ZIrr (↥L) :=
    OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  obtain ⟨e, he⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨η, hηirr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨η, hηirr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = η from rfl] at he
  -- `χ₁ − a•η₁` is supported on `H^#`.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  -- reciprocity: `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, R⟩`.
  have hrec := hyp.inner_tau_eq_inner_restrict hsupp (hyp.coherentYset.extension η)
  refine ⟨cc - a * e, ?_, ?_⟩
  · rw [hrec, ClassFunction.inner_sub_left, ← Nat.cast_smul_eq_nsmul ℂ a η,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_conj_symm _ χ₁, hcc,
      OddOrder.RepresentationTheory.inner_conj_symm _ η, he]
    simp only [star_intCast]
    push_cast; ring
  · exact dvd_sub hacc (dvd_mul_right _ _)

/-- **(6.8.1) `a ∣ b`**, case (A) / c2 mirror of
`dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius`.
The `a ∣ c` input uses the case-(A) `dvd_inner_restrict_extension_Yset_c2_caseA`
(cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem dvd_inner_tau_scaledDiff_extension_Yset_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ bb : ℤ,
      ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.coherentYset.extension η) = (bb : ℂ)
        ∧ (a : ℤ) ∣ bb := by
  classical
  -- step 2: `c = ⟨R, χ₁⟩` is an integer with `a ∣ c`.
  obtain ⟨cc, hcc, hacc⟩ :=
    hyp.dvd_inner_restrict_extension_Yset_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ ha_pos ha
  -- `R ∈ ZIrr L`, `η₁` irreducible ⟹ `e := ⟨R, η₁⟩ ∈ ℤ`.
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : ClassFunction.restrict L (hyp.coherentYset.extension η) ∈ ZIrr (↥L) :=
    OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  obtain ⟨e, he⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨η, hηirr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨η, hηirr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = η from rfl] at he
  -- `χ₁ − a•η₁` is supported on `H^#`.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  -- reciprocity: `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, R⟩`.
  have hrec := hyp.inner_tau_eq_inner_restrict hsupp (hyp.coherentYset.extension η)
  refine ⟨cc - a * e, ?_, ?_⟩
  · rw [hrec, ClassFunction.inner_sub_left, ← Nat.cast_smul_eq_nsmul ℂ a η,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_conj_symm _ χ₁, hcc,
      OddOrder.RepresentationTheory.inner_conj_symm _ η, he]
    simp only [star_intCast]
    push_cast; ring
  · exact dvd_sub hacc (dvd_mul_right _ _)

/-- **(6.8.1) cross-diagonal/`Y`-difference isometry** (mmd 04.8 L166, the constancy ingredient of
decomposition (168)).  For `η = η₁`, `η' = η_j ∈ Y` with `η' ≠ η`, and an `X`-anchor `χ₁ ∈ X(Zc)`
with `χ₁(1) = a·|W₁|` (`a > 0`):
`⟨(χ₁−aη₁)^τ, (η_j−η₁)^τ⟩ = a`.

By the Dade isometry on the supported pair `{χ₁−aη₁, η_j−η₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`; `χ₁−aη₁` supported by
`sMember_scaledDiffSupport_of_charValue_eq`, `η_j−η₁` by `sMember_diffSupport_of_charValue_eq` at
the
common degree `|W₁|`), the inner product equals the source `⟨χ₁−aη₁, η_j−η₁⟩`, which expands by
`X ⊥ Y` (`⟨χ₁,η_j⟩ = ⟨χ₁,η₁⟩ = 0`) and `Y`-orthonormality (`⟨η₁,η_j⟩ = 0`, `⟨η₁,η₁⟩ = 1`) to
`a·⟨η₁,η₁⟩ = a`.  This gives the constancy `β_j − β₁ = a` (j>1) of the `η_j^{τ₁}`-coefficients
`β_j = ⟨(χ₁−aη₁)^τ, η_j^{τ₁}⟩` of decomposition (168). -/
theorem inner_tau_scaledDiff_tau_Yset_diff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η' ≠ η)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (η' - η)) = (a : ℂ) := by
  classical
  -- irreducibility + disjointness `X(Zc) ⊥ Y`.
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported difference inputs.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsuppX : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  have hsuppY : (η' - η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη') (hyp.Yset_subset_S hη)
      ((hyp.Yset_apply_one hη').trans (hyp.Yset_apply_one hη).symm)
  -- Dade isometry on the supported pair.
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade (S := ({χ₁ - a • η, η' - η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppY)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- the source orthogonality computation `⟨χ₁ − a•η, η' − η⟩ = a`.
  have hXY : ∀ ψ ∈ hyp.Yset, ClassFunction.inner χ₁ ψ = 0 := by
    intro ψ hψ
    exact inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hXirr φ hφ) (fun φ hφ => hYirr φ hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      ψ (Submodule.subset_span hψ)
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hYirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hYirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXY η' hη', hXY η hη, hYon η η' hη hη', hYon η η hη hη, if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.1) cross-diagonal/`Y`-difference isometry**, case (A) / c2 mirror of
`inner_tau_scaledDiff_tau_Yset_diff_of_frobenius`.  `X`-irreducibility comes from the certain-type
input `isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem inner_tau_scaledDiff_tau_Yset_diff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η' ≠ η)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (η' - η)) = (a : ℂ) := by
  classical
  -- irreducibility + disjointness `X(Zc) ⊥ Y`.
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported difference inputs.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsuppX : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  have hsuppY : (η' - η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη') (hyp.Yset_subset_S hη)
      ((hyp.Yset_apply_one hη').trans (hyp.Yset_apply_one hη).symm)
  -- Dade isometry on the supported pair.
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade (S := ({χ₁ - a • η, η' - η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppY)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- the source orthogonality computation `⟨χ₁ − a•η, η' − η⟩ = a`.
  have hXY : ∀ ψ ∈ hyp.Yset, ClassFunction.inner χ₁ ψ = 0 := by
    intro ψ hψ
    exact inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hXirr φ hφ) (fun φ hφ => hYirr φ hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      ψ (Submodule.subset_span hψ)
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hYirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hYirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXY η' hη', hXY η hη, hYon η η' hη hη', hYon η η hη hη, if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.1) norm of the cross-diagonal image** (mmd 04.8 L176: `‖χ₁−aη₁‖² = 1+a²`).  For
`η = η₁ ∈ Y`
and an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`:
`⟨(χ₁−aη₁)^τ, (χ₁−aη₁)^τ⟩ = 1 + a²`.

By the Dade isometry on the supported singleton `{χ₁−aη₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`) this equals the source norm
`⟨χ₁−aη₁, χ₁−aη₁⟩`, which expands by `χ₁`/`η₁`-orthonormality (`⟨χ₁,χ₁⟩ = ⟨η₁,η₁⟩ = 1`) and `X ⊥ Y`
(`⟨χ₁,η₁⟩ = ⟨η₁,χ₁⟩ = 0`) to `1 + a²`.  This is the LHS of Peterfalvi's norm identity
`1+a² = ‖X‖² + (b−a)² + (m−1)b²` for the `b = 0` step. -/
theorem inner_self_tau_scaledDiff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (χ₁ - a • η)) = 1 + (a : ℂ) ^ 2 := by
  classical
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- orthonormality / orthogonality scalars.
  have hχ₁n : ClassFunction.inner χ₁ χ₁ = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
      (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hηn : ClassFunction.inner η η = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hXY : ClassFunction.inner χ₁ η = (0 : ℂ) :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      η (Submodule.subset_span hη)
  have hYX : ClassFunction.inner η χ₁ = (0 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm χ₁ η, hXY, star_zero]
  -- supported singleton ⟹ Dade isometry.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade (S := ({χ₁ - a • η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs; rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hsupp)
    (Submodule.subset_span rfl) (Submodule.subset_span rfl)
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hχ₁n, hηn,
    hXY, hYX, star_natCast]
  ring

/-- **(6.8.1) norm of the cross-diagonal image**, case (A) / c2 mirror of
`inner_self_tau_scaledDiff_of_frobenius`.  `X`-irreducibility comes from the certain-type input
`isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem inner_self_tau_scaledDiff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (χ₁ - a • η)) = 1 + (a : ℂ) ^ 2 := by
  classical
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- orthonormality / orthogonality scalars.
  have hχ₁n : ClassFunction.inner χ₁ χ₁ = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
      (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hηn : ClassFunction.inner η η = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hXY : ClassFunction.inner χ₁ η = (0 : ℂ) :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      η (Submodule.subset_span hη)
  have hYX : ClassFunction.inner η χ₁ = (0 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm χ₁ η, hXY, star_zero]
  -- supported singleton ⟹ Dade isometry.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη)
      hdeg
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade (S := ({χ₁ - a • η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs; rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hsupp)
    (Submodule.subset_span rfl) (Submodule.subset_span rfl)
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hχ₁n, hηn,
    hXY, hYX, star_natCast]
  ring

/-- **(6.8.1) the degree ratio `a` satisfies `a ≥ 2`** (mmd 04.8 L176: "Since `X ∩ Y = ∅`,
`a > 1`").
For an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, the ratio `a ≥ 2`.

If `a ≤ 1` then (as `χ₁` is a positive-degree irreducible, `a ≥ 1`, so) `a = 1`, hence the source
`θ` (with `χ₁ = Ind_H^L θ`, `θ ≠ 1`, `χ₁(1) = |W₁|·θ(1)`) has degree `θ(1) = a = 1`, so `θ` is a
nontrivial **linear** character (`exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one`); then
`χ₁ = Ind_H^L θ ∈ Y = S(H')` (`mem_Yset_iff_exists_linear_source`), contradicting `χ₁ ∈ X` and the
disjointness `X(Zc) ∩ Y = ∅`.  This is the `2 ≤ a` input of
`eq_zero_or_edge_of_dvd_of_normBound`. -/
theorem two_le_degreeRatio_of_mem_Xset_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) : 2 ≤ a := by
  classical
  -- extract the source `θ` of `χ₁ ∈ S`.
  have hχ₁S : χ₁ ∈ hyp.S := hyp.Xset_subset_S hχ₁
  rw [hyp.S_eq] at hχ₁S
  obtain ⟨θ, hθne, hχ₁eq⟩ := hχ₁S
  -- `χ₁(1) = |W₁|·θ(1)`.
  have hdeg : χ₁ 1 = (Nat.card hyp.W1 : ℂ) * (θ : ClassFunction ↥H ℂ) 1 := by
    rw [hχ₁eq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
      hyp.index_H_eq_card_W1]
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- `(a : ℂ) = θ(1)`.
  have haθ : (a : ℂ) = (θ : ClassFunction ↥H ℂ) 1 := by
    have h : (a : ℂ) * (Nat.card hyp.W1 : ℂ)
        = (θ : ClassFunction ↥H ℂ) 1 * (Nat.card hyp.W1 : ℂ) := by rw [← ha, hdeg]; ring
    exact mul_right_cancel₀ hW1ne h
  -- `θ(1) = d > 0`, so `a = d ≥ 1`.
  obtain ⟨d, hd_pos, hd_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have had : a = d := by have := haθ.trans hd_eq; exact_mod_cast this
  by_contra hlt
  push Not at hlt
  -- `a ≤ 1` with `a = d ≥ 1` ⟹ `a = 1` ⟹ `θ(1) = 1`.
  have ha1 : a = 1 := by omega
  have hθ1 : (θ : ClassFunction ↥H ℂ) 1 = 1 := by rw [← haθ, ha1]; norm_num
  -- `θ` is a nontrivial linear character ⟹ `χ₁ ∈ Y`, contradicting `χ₁ ∈ X`.
  obtain ⟨ψ, hψeq⟩ := θ.2.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one hθ1
  have hlinθ : OddOrder.RepresentationTheory.linearIrreducibleCharacter ψ = θ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.ext hψeq
  have hψne : ψ ≠ 1 := by
    intro hψ1
    apply hθne
    rw [← hlinθ, hψ1]
    exact OddOrder.RepresentationTheory.linearIrreducibleCharacter_eq_trivial_iff.mpr rfl
  have hχ₁Y : χ₁ ∈ hyp.Yset := by
    rw [hyp.mem_Yset_iff_exists_linear_source]
    exact ⟨ψ, hψne, by rw [hχ₁eq, hψeq]⟩
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  exact absurd hχ₁Y (Set.disjoint_left.mp hdisj hχ₁)

open scoped Classical in
/-- **(6.8.1) step-4 dichotomy** (mmd 04.8 L176, "`b ≡ c ≡ 0 (mod a)` ⟹ `b = 0` or the `m=2`
edge").  For `η₁ ∈ Y` and an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, the
`η₁^{τ₁}`-coefficient `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩` (Peterfalvi's `b − a`) is either `−a` (the `b = 0`
case) or `0` with
`|Y| = 2` (the `b = a ∧ m = 2` edge case).

Bessel's inequality (`sum_sq_le_inner_self_re`) over the orthonormal `Y^{τ₁}`-family with
`v = (χ₁−aη₁)^τ`: the coefficient is `bb = ⟨v,η₁^{τ₁}⟩` (`= b−a`, `a ∣ bb`, step 3) on `η₁^{τ₁}`
and `bb + a` on the other `m−1` members (the constancy
`inner_tau_scaledDiff_tau_Yset_diff_of_frobenius`); their squares sum to
`bb² + (m−1)(bb+a)² ≤ ‖v‖² = 1 + a²` (norm `inner_self_tau_scaledDiff_of_frobenius`).  With
`a ∣ (bb+a)`, `2 ≤ a` (`two_le_degreeRatio_of_mem_Xset_of_frobenius`), `2 ≤ m`
(`two_le_Yset_ncard`), `eq_zero_or_edge_of_dvd_of_normBound` gives
`bb+a = 0 ∨ (bb+a = a ∧ m = 2)`. -/
theorem coeff_eq_neg_or_edge_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = -(a : ℂ)
      ∨ (hyp.Yset.ncard = 2 ∧
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = 0) := by
  classical
  -- step 3: `bb = ⟨v, η₁^{τ₁}⟩ ∈ ℤ`, `a ∣ bb`.
  obtain ⟨bb, hbb, habb⟩ :=
    hyp.dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha
  -- `Y`-orthonormality and injectivity of the extension on `Y`.
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Yset hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Yset hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hEinj : ∀ η ∈ hyp.Yset, ∀ η' ∈ hyp.Yset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' := by
    intro η hη η' hη' heq
    by_contra hne
    have h0 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 0 := by
      rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span hη)
        (Submodule.subset_span hη'), hYon η η' hη hη', if_neg hne]
    have h1 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 1 := by
      rw [heq, hyp.coherentYset.extension_inner_eq η' η' (Submodule.subset_span hη')
        (Submodule.subset_span hη'), hYon η' η' hη' hη', if_pos rfl]
    rw [h1] at h0; exact one_ne_zero h0
  -- coefficient values `⟨v, η^{τ₁}⟩`.
  have hcoeff : ∀ η ∈ hyp.Yset,
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η)
        = ((if η = η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro η hη
    by_cases hee : η = η₁
    · subst hee; rw [if_pos rfl]; exact hbb
    · rw [if_neg hee]
      have hsuppd : (η - η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
        hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
          ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
      have htaud : hyp.tau (η - η₁)
          = hyp.coherentYset.extension η - hyp.coherentYset.extension η₁ := by
        rw [← hyp.coherentYset.extends_on_supported (η - η₁)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
          map_sub]
      have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_of_frobenius hF hη₁ hη hee hχ₁ ha
      rw [htaud, ClassFunction.inner_sub_right, hbb] at hconst
      push_cast
      linear_combination hconst
  -- the orthonormal `Y^{τ₁}`-image Finset.
  have hmemt : ∀ {η}, η ∈ hyp.Yset_finite.toFinset ↔ η ∈ hyp.Yset :=
    fun {η} => hyp.Yset_finite.mem_toFinset
  have hEinj_t : ∀ η ∈ hyp.Yset_finite.toFinset, ∀ η' ∈ hyp.Yset_finite.toFinset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' :=
    fun η hη η' hη' => hEinj η (hmemt.mp hη) η' (hmemt.mp hη')
  have horth : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ∀ ψ' ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ hψ ψ' hψ'
    rw [Finset.mem_image] at hψ hψ'
    obtain ⟨η, hη, rfl⟩ := hψ
    obtain ⟨η', hη', rfl⟩ := hψ'
    rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span (hmemt.mp hη))
      (Submodule.subset_span (hmemt.mp hη')), hYon η η' (hmemt.mp hη) (hmemt.mp hη')]
    by_cases hee : η = η'
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η' hη' h))]
  have hη₁t : η₁ ∈ hyp.Yset_finite.toFinset := hmemt.mpr hη₁
  have hβval : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) ψ
        = ((if ψ = hyp.coherentYset.extension η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro ψ hψ
    rw [Finset.mem_image] at hψ
    obtain ⟨η, hη, rfl⟩ := hψ
    rw [hcoeff η (hmemt.mp hη)]
    by_cases hee : η = η₁
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h))]
  -- Bessel + norm ⟹ the integer norm inequality.
  have hbessel := OddOrder.RepresentationTheory.sum_sq_le_inner_self_re horth
    (hyp.tau (χ₁ - a • η₁)) hβval
  have hnorm_re : (ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₁ - a • η₁))).re
      = ((1 + a ^ 2 : ℕ) : ℝ) := by
    rw [hyp.inner_self_tau_scaledDiff_of_frobenius hF hη₁ hχ₁ ha,
      show (1 : ℂ) + (a : ℂ) ^ 2 = ((1 + a ^ 2 : ℕ) : ℂ) by push_cast; ring, Complex.natCast_re]
  rw [hnorm_re] at hbessel
  have hsum : ∑ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      (if ψ = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
      = bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 := by
    rw [Finset.sum_image hEinj_t]
    have hsplit : ∀ η ∈ hyp.Yset_finite.toFinset,
        (if hyp.coherentYset.extension η = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
        = if η = η₁ then bb ^ 2 else (bb + a) ^ 2 := by
      intro η hη
      by_cases hee : η = η₁
      · subst hee; simp
      · rw [if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h)), if_neg hee]
    rw [Finset.sum_congr rfl hsplit, ← Finset.add_sum_erase _ _ hη₁t, if_pos rfl]
    have hc : (hyp.Yset_finite.toFinset.erase η₁).card = hyp.Yset.ncard - 1 := by
      rw [Finset.card_erase_of_mem hη₁t, ← Set.ncard_eq_toFinset_card _ hyp.Yset_finite]
    have h1le : 1 ≤ hyp.Yset.ncard := by
      rw [Set.ncard_eq_toFinset_card _ hyp.Yset_finite]; exact Finset.one_le_card.mpr ⟨η₁, hη₁t⟩
    rw [Finset.sum_congr rfl (fun η hη => if_neg (Finset.ne_of_mem_erase hη)),
      Finset.sum_const, nsmul_eq_mul, hc, Nat.cast_sub h1le, Nat.cast_one]
  rw [hsum] at hbessel
  -- the integer inequality and `eq_zero_or_edge`.
  have hnorm_ineq : bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 ≤ 1 + (a : ℤ) ^ 2 := by
    exact_mod_cast hbessel
  have ha2 : (2 : ℤ) ≤ (a : ℤ) := by
    exact_mod_cast hyp.two_le_degreeRatio_of_mem_Xset_of_frobenius hχ₁ ha
  have hm2 : (2 : ℤ) ≤ (hyp.Yset.ncard : ℤ) := by exact_mod_cast hyp.two_le_Yset_ncard
  have hnorm_lemma : ((bb + a) - (a : ℤ)) ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2
      ≤ 1 + (a : ℤ) ^ 2 := by
    rw [show (bb + (a : ℤ)) - (a : ℤ) = bb by ring]; exact hnorm_ineq
  have hdich := eq_zero_or_edge_of_dvd_of_normBound ha2 hm2 (dvd_add habb (dvd_refl _)) hnorm_lemma
  -- translate `bb+a = 0 ∨ (bb+a = a ∧ m = 2)` to the coefficient dichotomy.
  rcases hdich with h | ⟨h1, h2⟩
  · left
    rw [hbb]
    have : bb = -(a : ℤ) := by omega
    rw [this]; push_cast; ring
  · right
    refine ⟨by exact_mod_cast h2, ?_⟩
    rw [hbb]
    have : bb = 0 := by omega
    rw [this]; norm_num

open scoped Classical in
/-- **(6.8.1) step-4 dichotomy**, case (A) / c2 mirror of `coeff_eq_neg_or_edge_of_frobenius`.
The divisibility/constancy/norm inputs use their case-(A) counterparts
(`dvd_inner_tau_scaledDiff_extension_Yset_c2_caseA`, `inner_tau_scaledDiff_tau_Yset_diff_c2_caseA`,
`inner_self_tau_scaledDiff_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem coeff_eq_neg_or_edge_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = -(a : ℂ)
      ∨ (hyp.Yset.ncard = 2 ∧
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η₁) = 0) := by
  classical
  -- step 3: `bb = ⟨v, η₁^{τ₁}⟩ ∈ ℤ`, `a ∣ bb`.
  obtain ⟨bb, hbb, habb⟩ :=
    hyp.dvd_inner_tau_scaledDiff_extension_Yset_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos
        ha
  -- `Y`-orthonormality and injectivity of the extension on `Y`.
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Yset hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Yset hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hEinj : ∀ η ∈ hyp.Yset, ∀ η' ∈ hyp.Yset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' := by
    intro η hη η' hη' heq
    by_contra hne
    have h0 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 0 := by
      rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span hη)
        (Submodule.subset_span hη'), hYon η η' hη hη', if_neg hne]
    have h1 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 1 := by
      rw [heq, hyp.coherentYset.extension_inner_eq η' η' (Submodule.subset_span hη')
        (Submodule.subset_span hη'), hYon η' η' hη' hη', if_pos rfl]
    rw [h1] at h0; exact one_ne_zero h0
  -- coefficient values `⟨v, η^{τ₁}⟩`.
  have hcoeff : ∀ η ∈ hyp.Yset,
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.coherentYset.extension η)
        = ((if η = η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro η hη
    by_cases hee : η = η₁
    · subst hee; rw [if_pos rfl]; exact hbb
    · rw [if_neg hee]
      have hsuppd : (η - η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
        hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
          ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
      have htaud : hyp.tau (η - η₁)
          = hyp.coherentYset.extension η - hyp.coherentYset.extension η₁ := by
        rw [← hyp.coherentYset.extends_on_supported (η - η₁)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
          map_sub]
      have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_c2_caseA hK hW1 hA hη₁ hη hee hχ₁ ha
      rw [htaud, ClassFunction.inner_sub_right, hbb] at hconst
      push_cast
      linear_combination hconst
  -- the orthonormal `Y^{τ₁}`-image Finset.
  have hmemt : ∀ {η}, η ∈ hyp.Yset_finite.toFinset ↔ η ∈ hyp.Yset :=
    fun {η} => hyp.Yset_finite.mem_toFinset
  have hEinj_t : ∀ η ∈ hyp.Yset_finite.toFinset, ∀ η' ∈ hyp.Yset_finite.toFinset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' :=
    fun η hη η' hη' => hEinj η (hmemt.mp hη) η' (hmemt.mp hη')
  have horth : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ∀ ψ' ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ hψ ψ' hψ'
    rw [Finset.mem_image] at hψ hψ'
    obtain ⟨η, hη, rfl⟩ := hψ
    obtain ⟨η', hη', rfl⟩ := hψ'
    rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span (hmemt.mp hη))
      (Submodule.subset_span (hmemt.mp hη')), hYon η η' (hmemt.mp hη) (hmemt.mp hη')]
    by_cases hee : η = η'
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η' hη' h))]
  have hη₁t : η₁ ∈ hyp.Yset_finite.toFinset := hmemt.mpr hη₁
  have hβval : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) ψ
        = ((if ψ = hyp.coherentYset.extension η₁ then bb else bb + a : ℤ) : ℂ) := by
    intro ψ hψ
    rw [Finset.mem_image] at hψ
    obtain ⟨η, hη, rfl⟩ := hψ
    rw [hcoeff η (hmemt.mp hη)]
    by_cases hee : η = η₁
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h))]
  -- Bessel + norm ⟹ the integer norm inequality.
  have hbessel := OddOrder.RepresentationTheory.sum_sq_le_inner_self_re horth
    (hyp.tau (χ₁ - a • η₁)) hβval
  have hnorm_re : (ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₁ - a • η₁))).re
      = ((1 + a ^ 2 : ℕ) : ℝ) := by
    rw [hyp.inner_self_tau_scaledDiff_c2_caseA hK hW1 hA hη₁ hχ₁ ha,
      show (1 : ℂ) + (a : ℂ) ^ 2 = ((1 + a ^ 2 : ℕ) : ℂ) by push_cast; ring, Complex.natCast_re]
  rw [hnorm_re] at hbessel
  have hsum : ∑ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      (if ψ = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
      = bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 := by
    rw [Finset.sum_image hEinj_t]
    have hsplit : ∀ η ∈ hyp.Yset_finite.toFinset,
        (if hyp.coherentYset.extension η = hyp.coherentYset.extension η₁ then bb else bb + a) ^ 2
        = if η = η₁ then bb ^ 2 else (bb + a) ^ 2 := by
      intro η hη
      by_cases hee : η = η₁
      · subst hee; simp
      · rw [if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h)), if_neg hee]
    rw [Finset.sum_congr rfl hsplit, ← Finset.add_sum_erase _ _ hη₁t, if_pos rfl]
    have hc : (hyp.Yset_finite.toFinset.erase η₁).card = hyp.Yset.ncard - 1 := by
      rw [Finset.card_erase_of_mem hη₁t, ← Set.ncard_eq_toFinset_card _ hyp.Yset_finite]
    have h1le : 1 ≤ hyp.Yset.ncard := by
      rw [Set.ncard_eq_toFinset_card _ hyp.Yset_finite]; exact Finset.one_le_card.mpr ⟨η₁, hη₁t⟩
    rw [Finset.sum_congr rfl (fun η hη => if_neg (Finset.ne_of_mem_erase hη)),
      Finset.sum_const, nsmul_eq_mul, hc, Nat.cast_sub h1le, Nat.cast_one]
  rw [hsum] at hbessel
  -- the integer inequality and `eq_zero_or_edge`.
  have hnorm_ineq : bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2 ≤ 1 + (a : ℤ) ^ 2 := by
    exact_mod_cast hbessel
  have ha2 : (2 : ℤ) ≤ (a : ℤ) := by
    exact_mod_cast hyp.two_le_degreeRatio_of_mem_Xset_of_frobenius hχ₁ ha
  have hm2 : (2 : ℤ) ≤ (hyp.Yset.ncard : ℤ) := by exact_mod_cast hyp.two_le_Yset_ncard
  have hnorm_lemma : ((bb + a) - (a : ℤ)) ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + a) ^ 2
      ≤ 1 + (a : ℤ) ^ 2 := by
    rw [show (bb + (a : ℤ)) - (a : ℤ) = bb by ring]; exact hnorm_ineq
  have hdich := eq_zero_or_edge_of_dvd_of_normBound ha2 hm2 (dvd_add habb (dvd_refl _)) hnorm_lemma
  -- translate `bb+a = 0 ∨ (bb+a = a ∧ m = 2)` to the coefficient dichotomy.
  rcases hdich with h | ⟨h1, h2⟩
  · left
    rw [hbb]
    have : bb = -(a : ℤ) := by omega
    rw [this]; push_cast; ring
  · right
    refine ⟨by exact_mod_cast h2, ?_⟩
    rw [hbb]
    have : bb = 0 := by omega
    rw [this]; norm_num

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08


