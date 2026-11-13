-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_RestrictExtensionDvd
-- name    : OddOrder_Peterfalvi_S08_RestrictExtensionDvd
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:45:14.523035+00:00
-- url     : https://prove2.me/theorems/d66917cf-da25-4910-9384-0479a33e06a5
-- title:
--   Peterfalvi (6.8.1): restriction/extension divisibility, good-case structure
-- statement:
--   Part of the Peterfalvi §8 coherence core covering the good case of steps 4 and 5 of (6.8.1).
--
--   Main results: `orthogonal_normOne_tau_scaledDiff_add_extension_general` (the good-case $X$-structure), `inner_extension_Xset_sub_eq_neg_one_general` (the step-5 inner-product relation) and `extension_eq_or_eq_neg_general` (the step-5 dichotomy $X=\chi_1^{\tau_2}$ or $X=-\chi_2^{\tau_2}$), each with a case-(A)/c2 mirror.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_RestrictExtensionDvd.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_RestrictExtensionDvd.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_XBlockCounting
import Definitions.Def_OddOrder_Peterfalvi_S08_SibleyRestrictionLemmas

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **(6.8.1) step-4 good-case `X`-structure** (mmd 04.8 L176: "`b = 0` ⟹
`(χ₁ − aη₁)^τ = X − aη₁^{τ₁}`, `‖X‖² = ‖χ₁‖² = 1`").  In the good case
`⟨(χ₁ − aη₁)^τ, η₁^{τ₁}⟩ = −a` (the `b = 0` branch of `coeff_eq_neg_or_edge_of_frobenius`), the
element `X := (χ₁ − aη₁)^τ + a·η₁^{τ₁}` is orthogonal to the whole coherent `Y`-image family
`Y^{τ₁}`, has norm `1`, and lies in `ℤ[Irr G]`.  Step 5 then identifies `X = χ₁^{τ₂}`, giving the
crux `(χ₁ − aη₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}`.

The orthogonality uses the constancy `inner_tau_scaledDiff_tau_Yset_diff_of_frobenius`
(`⟨v, (η − η₁)^τ⟩ = a`, so `⟨v, η^{τ₁}⟩ = ⟨v, η₁^{τ₁}⟩ + a = 0` for `η ≠ η₁`) and the norm
`‖v‖² = 1 + a²` (`inner_self_tau_scaledDiff_of_frobenius`); the norm of `X` is
`(1 + a²) − a² − a² + a² = 1`. -/
theorem orthogonal_normOne_tau_scaledDiff_add_extension_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (cY.extension η) = 0)
      ∧ ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) = 1
      ∧ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- Y-image orthonormality: `⟨η^{τ₁}, η'^{τ₁}⟩ = ⟨η, η'⟩ = δ`.
  have hYon : ∀ η η', η ∈ hyp.Yset → η' ∈ hyp.Yset →
      ClassFunction.inner (cY.extension η) (cY.extension η')
        = if η = η' then (1 : ℂ) else 0 := by
    intro η η' hη hη'
    rw [cY.extension_inner_eq η η' (Submodule.subset_span hη)
      (Submodule.subset_span hη')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η', hyp.isIrreducibleCharacter_of_mem_Yset hη'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  -- `⟨v, η^{τ₁}⟩ = 0` for `η ≠ η₁` (constancy `⟨v, (η−η₁)^τ⟩ = a` plus `⟨v, η₁^{τ₁}⟩ = −a`).
  have hcoeff0 : ∀ η ∈ hyp.Yset, η ≠ η₁ →
      ClassFunction.inner v (cY.extension η) = 0 := by
    intro η hη hne
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_of_frobenius hF hη₁ hη hne hχ₁ ha
    have hsuppd : (η - η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
        ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
    have htaud : hyp.tau (η - η₁)
        = cY.extension η - cY.extension η₁ := by
      rw [← cY.extends_on_supported (η - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hgood] at hconst
    linear_combination hconst
  -- norm and the conjugate of the good-case coefficient.
  have hvv : ClassFunction.inner v v = 1 + (a : ℂ) ^ 2 :=
    hyp.inner_self_tau_scaledDiff_of_frobenius hF hη₁ hχ₁ ha
  have he₁e₁ : ClassFunction.inner (cY.extension η₁)
      (cY.extension η₁) = 1 := by rw [hYon η₁ η₁ hη₁ hη₁, if_pos rfl]
  have he₁v : ClassFunction.inner (cY.extension η₁) v = -(a : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm v (cY.extension η₁), hgood]
    simp
  refine ⟨?_, ?_, ?_⟩
  · -- orthogonality `⟨X, η^{τ₁}⟩ = 0`.
    intro η hη
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left]
    by_cases hee : η = η₁
    · subst hee
      rw [hgood, he₁e₁]; ring
    · rw [hcoeff0 η hη hee, hYon η₁ η hη₁ hη, if_neg (fun h => hee h.symm)]; ring
  · -- norm `⟨X, X⟩ = 1`.
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
    rw [hvv, hgood, he₁v, he₁e₁, star_natCast]; ring
  · -- `X ∈ ℤ[Irr G]`.
    have hdeg : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
    have hsuppX : (χ₁ - a • η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁)
        (hyp.Yset_subset_S hη₁) hdeg
    have hsrcZ : χ₁ - a • η₁ ∈ ZIrr (↥L) :=
      sub_mem (hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁).mem_ZIrr
        (nsmul_mem (hyp.isIrreducibleCharacter_of_mem_Yset hη₁).mem_ZIrr a)
    have hvZ : v ∈ ZIrr G := by
      rw [hv]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.dade hsuppX hsrcZ
    have he₁Z : cY.extension η₁ ∈ ZIrr G :=
      cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)
    have haZ : (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem he₁Z a
    exact add_mem hvZ haZ

open scoped Classical in
/-- **(6.8.1) step-4 good-case `X`-structure**, case (A) / c2 mirror of
`orthogonal_normOne_tau_scaledDiff_add_extension_general`.  The constancy/norm/`X`-irreducibility
inputs use their case-(A) counterparts (`inner_tau_scaledDiff_tau_Yset_diff_c2_caseA`,
`inner_self_tau_scaledDiff_c2_caseA`, `isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF`
(cert data `hK`/`hW1`/`hA`). -/
theorem orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (cY.extension η) = 0)
      ∧ ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
          (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) = 1
      ∧ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- Y-image orthonormality: `⟨η^{τ₁}, η'^{τ₁}⟩ = ⟨η, η'⟩ = δ`.
  have hYon : ∀ η η', η ∈ hyp.Yset → η' ∈ hyp.Yset →
      ClassFunction.inner (cY.extension η) (cY.extension η')
        = if η = η' then (1 : ℂ) else 0 := by
    intro η η' hη hη'
    rw [cY.extension_inner_eq η η' (Submodule.subset_span hη)
      (Submodule.subset_span hη')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η', hyp.isIrreducibleCharacter_of_mem_Yset hη'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  -- `⟨v, η^{τ₁}⟩ = 0` for `η ≠ η₁` (constancy `⟨v, (η−η₁)^τ⟩ = a` plus `⟨v, η₁^{τ₁}⟩ = −a`).
  have hcoeff0 : ∀ η ∈ hyp.Yset, η ≠ η₁ →
      ClassFunction.inner v (cY.extension η) = 0 := by
    intro η hη hne
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_c2_caseA hK hW1 hA hη₁ hη hne hχ₁ ha
    have hsuppd : (η - η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
        ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
    have htaud : hyp.tau (η - η₁)
        = cY.extension η - cY.extension η₁ := by
      rw [← cY.extends_on_supported (η - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hgood] at hconst
    linear_combination hconst
  -- norm and the conjugate of the good-case coefficient.
  have hvv : ClassFunction.inner v v = 1 + (a : ℂ) ^ 2 :=
    hyp.inner_self_tau_scaledDiff_c2_caseA hK hW1 hA hη₁ hχ₁ ha
  have he₁e₁ : ClassFunction.inner (cY.extension η₁)
      (cY.extension η₁) = 1 := by rw [hYon η₁ η₁ hη₁ hη₁, if_pos rfl]
  have he₁v : ClassFunction.inner (cY.extension η₁) v = -(a : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm v (cY.extension η₁), hgood]
    simp
  refine ⟨?_, ?_, ?_⟩
  · -- orthogonality `⟨X, η^{τ₁}⟩ = 0`.
    intro η hη
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left]
    by_cases hee : η = η₁
    · subst hee
      rw [hgood, he₁e₁]; ring
    · rw [hcoeff0 η hη hee, hYon η₁ η hη₁ hη, if_neg (fun h => hee h.symm)]; ring
  · -- norm `⟨X, X⟩ = 1`.
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
    rw [hvv, hgood, he₁v, he₁e₁, star_natCast]; ring
  · -- `X ∈ ℤ[Irr G]`.
    have hdeg : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
    have hsuppX : (χ₁ - a • η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁)
        (hyp.Yset_subset_S hη₁) hdeg
    have hsrcZ : χ₁ - a • η₁ ∈ ZIrr (↥L) :=
      sub_mem (hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁).mem_ZIrr
        (nsmul_mem (hyp.isIrreducibleCharacter_of_mem_Yset hη₁).mem_ZIrr a)
    have hvZ : v ∈ ZIrr G := by
      rw [hv]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.dade hsuppX hsrcZ
    have he₁Z : cY.extension η₁ ∈ ZIrr G :=
      cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)
    have haZ : (a : ℂ) • cY.extension η₁ ∈ ZIrr G := by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem he₁Z a
    exact add_mem hvZ haZ

/-- **(6.8.1) `X`-difference isometry** (mmd 04.8 L176, the step-5 input).  For `η₁ ∈ Y`, an
`X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, and a second `X`-member `χ₂ ∈ X(Zc)`, `χ₂ ≠ χ₁`, of
the **same degree** `χ₂(1) = χ₁(1)`:
`⟨(χ₁−aη₁)^τ, (χ₂−χ₁)^τ⟩ = −1`.

By the Dade isometry on the supported pair `{χ₁−aη₁, χ₂−χ₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`; `χ₂−χ₁` supported by
`sMember_diffSupport_of_charValue_eq` at the common degree), the inner product equals the source
`⟨χ₁−aη₁, χ₂−χ₁⟩`, which expands by `X`-orthonormality (`⟨χ₁,χ₂⟩=0`, `⟨χ₁,χ₁⟩=1`) and `X ⊥ Y`
(`⟨η₁,χ₂⟩=⟨η₁,χ₁⟩=0`) to `(0 − a·0) − (1 − a·0) = −1`.  Combined with `himg_ortho`
(`η₁^{τ₁} ⊥ X^{τ₂}`) and the `X`-coherence `(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}`, this gives
`⟨X, χ₂^{τ₂}⟩ − ⟨X, χ₁^{τ₂}⟩ = −1` for the step-5 element `X` (good case), pinning `X = χ₁^{τ₂}`. -/
theorem inner_tau_scaledDiff_tau_Xset_diff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₂ - χ₁)) = -1 := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported inputs.
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX2 : (χ₂ - χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade (S := ({χ₁ - a • η₁, χ₂ - χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX2)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- source orthogonality `⟨χ₁ − a•η₁, χ₂ − χ₁⟩ = −1`.
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hXirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hXirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hYXz : ∀ ψ ∈ hyp.Xset hyp.centralCommutator, ClassFunction.inner η₁ ψ = 0 := by
    intro ψ hψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ η₁,
      inner_eq_zero_of_mem_span_of_disjoint_irreducible (fun φ hφ => hXirr φ hφ)
        (fun φ hφ => hYirr φ hφ) hdisj ψ (Submodule.subset_span hψ) η₁ (Submodule.subset_span hη₁),
      star_zero]
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXon χ₁ χ₂ hχ₁ hχ₂, hXon χ₁ χ₁ hχ₁ hχ₁, hYXz χ₂ hχ₂, hYXz χ₁ hχ₁,
    if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.1) `X`-difference isometry**, case (A) / c2 mirror of
`inner_tau_scaledDiff_tau_Xset_diff_of_frobenius`.  `X`-irreducibility comes from the certain-type
input `isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem inner_tau_scaledDiff_tau_Xset_diff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₂ - χ₁)) = -1 := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported inputs.
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX2 : (χ₂ - χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade (S := ({χ₁ - a • η₁, χ₂ - χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX2)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- source orthogonality `⟨χ₁ − a•η₁, χ₂ − χ₁⟩ = −1`.
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hXirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hXirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hYXz : ∀ ψ ∈ hyp.Xset hyp.centralCommutator, ClassFunction.inner η₁ ψ = 0 := by
    intro ψ hψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ η₁,
      inner_eq_zero_of_mem_span_of_disjoint_irreducible (fun φ hφ => hXirr φ hφ)
        (fun φ hφ => hYirr φ hφ) hdisj ψ (Submodule.subset_span hψ) η₁ (Submodule.subset_span hη₁),
      star_zero]
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXon χ₁ χ₂ hχ₁ hχ₂, hXon χ₁ χ₁ hχ₁ hχ₁, hYXz χ₂ hχ₂, hYXz χ₁ hχ₁,
    if_neg (Ne.symm hne), if_pos rfl]
  ring

open scoped Classical in
/-- **(6.8.1) step-5 inner-product relation** (mmd 04.8 L176).  For the good-case element
`X := (χ₁−aη₁)^τ + a·η₁^{τ₁}`, the `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`, and a second
equal-degree `X`-member `χ₂ ∈ X(Zc)`, `χ₂ ≠ χ₁`:
`⟨X, χ₂^{τ₂}⟩ − ⟨X, χ₁^{τ₂}⟩ = −1`.

`X = (χ₁−aη₁)^τ + a·η₁^{τ₁}` and `η₁^{τ₁} ⊥ X^{τ₂}` (himg_ortho
`inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`) give
`⟨X, χ_j^{τ₂}⟩ = ⟨(χ₁−aη₁)^τ, χ_j^{τ₂}⟩`; the `X`-coherence
`(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}` (`extends_on_supported` on the supported equal-degree difference)
and the isometry value `⟨(χ₁−aη₁)^τ, (χ₂−χ₁)^τ⟩ = −1`
(`inner_tau_scaledDiff_tau_Xset_diff_of_frobenius`) close it.  Together with `‖X‖² = 1` and Bessel
over the orthonormal `{χ₁^{τ₂}, χ₂^{τ₂}}`, this pins `X = χ₁^{τ₂}` (or `−χ₂^{τ₂}`, the `n = 2`
edge). -/
theorem inner_extension_Xset_sub_eq_neg_one_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₂)
      - ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁)
      = -1 := by
  classical
  set hXc := cX with hXc_def
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- `⟨X, χ_j^{τ₂}⟩ = ⟨v, χ_j^{τ₂}⟩` (himg_ortho `η₁^{τ₁} ⊥ X^{τ₂}`).
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (hXc.extension χ)
        = ClassFunction.inner v (hXc.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF cX cY hχ hη₁
    rw [← hXc_def] at h
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  -- `(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}` (X-coherence `extends_on_supported`).
  have hsuppX2 : (χ₂ - χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hXcoh : hyp.tau (χ₂ - χ₁) = hXc.extension χ₂ - hXc.extension χ₁ := by
    have h := hXc.extends_on_supported (χ₂ - χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₂) (Submodule.subset_span hχ₁), hsuppX2⟩
    rw [map_sub] at h
    exact h.symm
  -- isometry value `⟨v, (χ₂−χ₁)^τ⟩ = −1`.
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_diff_of_frobenius hF hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [hXcoh, ClassFunction.inner_sub_right] at hiso
  rw [hXv χ₂ hχ₂, hXv χ₁ hχ₁]
  exact hiso

open scoped Classical in
/-- **(6.8.1) step-5 inner-product relation**, case (A) / c2 mirror of
`inner_extension_Xset_sub_eq_neg_one_general`.  The himg_ortho/isometry inputs use their case-(A)
counterparts (`inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA`,
`inner_tau_scaledDiff_tau_Xset_diff_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem inner_extension_Xset_sub_eq_neg_one_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₂)
      - ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁)
      = -1 := by
  classical
  set hXc := cX with hXc_def
  set v := hyp.tau (χ₁ - a • η₁) with hv
  -- `⟨X, χ_j^{τ₂}⟩ = ⟨v, χ_j^{τ₂}⟩` (himg_ortho `η₁^{τ₁} ⊥ X^{τ₂}`).
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (hXc.extension χ)
        = ClassFunction.inner v (hXc.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA
      hK hW1 hA cX cY hχ hη₁
    rw [← hXc_def] at h
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  -- `(χ₂−χ₁)^τ = χ₂^{τ₂} − χ₁^{τ₂}` (X-coherence `extends_on_supported`).
  have hsuppX2 : (χ₂ - χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
  have hXcoh : hyp.tau (χ₂ - χ₁) = hXc.extension χ₂ - hXc.extension χ₁ := by
    have h := hXc.extends_on_supported (χ₂ - χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₂) (Submodule.subset_span hχ₁), hsuppX2⟩
    rw [map_sub] at h
    exact h.symm
  -- isometry value `⟨v, (χ₂−χ₁)^τ⟩ = −1`.
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_diff_c2_caseA hK hW1 hA hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [hXcoh, ClassFunction.inner_sub_right] at hiso
  rw [hXv χ₂ hχ₂, hXv χ₁ hχ₁]
  exact hiso

open scoped Classical in
/-- **(6.8.1) step-5 dichotomy `X = χ₁^{τ₂} ∨ X = −χ₂^{τ₂}`** (mmd 04.8 L176).  In the good case
`⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = −a`, the element `X := (χ₁−aη₁)^τ + a·η₁^{τ₁}` (norm `1`, `⊥ Y^{τ₁}`)
equals either `χ₁^{τ₂}` or `−χ₂^{τ₂}` for the second equal-degree anchor `χ₂`.

From the step-5 relation `⟨X,χ₂^{τ₂}⟩ − ⟨X,χ₁^{τ₂}⟩ = −1` (`inner_extension_Xset_sub_eq_neg_one`)
and Bessel `c₁² + c₂² ≤ ‖X‖² = 1` (`sum_sq_le_inner_self_re` over the orthonormal
`{χ₁^{τ₂},χ₂^{τ₂}}`, `c_j = ⟨X,χ_j^{τ₂}⟩ ∈ ℤ`), the integers satisfy `c₂−c₁=−1`, `c₁²+c₂²≤1`,
forcing `(1,0)` or `(0,−1)`; `⟨X,χ₁^{τ₂}⟩=1` (resp. `⟨X,−χ₂^{τ₂}⟩=1`) with both norm `1` gives
`X=χ₁^{τ₂}` (resp. `X=−χ₂^{τ₂}`) by positive-definiteness.  The `n=2` edge `X=−χ₂^{τ₂}` is
resolved by relabelling (deferred); for `n≥3` a third anchor pins `X=χ₁^{τ₂}`. -/
theorem extension_eq_or_eq_neg_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = cX.extension χ₁
      ∨ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = -cX.extension χ₂
      := by
  classical
  set hXc := cX with hXc_def
  set X := hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ with hX_def
  -- good-case structure: `‖X‖² = 1`, `X ∈ ZIrr` (fold the unfolded `X` from the good-case lemma).
  obtain ⟨_, hXnorm, hXZ⟩ := hyp.orthogonal_normOne_tau_scaledDiff_add_extension_general
    hF cY hη₁ hχ₁ ha hgood
  rw [← hX_def] at hXnorm hXZ
  -- `X`-image orthonormality, ZIrr membership, distinctness.
  have hX1Z : hXc.extension χ₁ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₁ (Submodule.subset_span hχ₁)
  have hX2Z : hXc.extension χ₂ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₂ (Submodule.subset_span hχ₂)
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (hXc.extension ψ) (hXc.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [hXc.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hX1norm : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₁) = 1 := by
    rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have hX2norm : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₂) = 1 := by
    rw [hXon χ₂ χ₂ hχ₂ hχ₂, if_pos rfl]
  have hX12 : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₂) = 0 := by
    rw [hXon χ₁ χ₂ hχ₁ hχ₂, if_neg (Ne.symm hne)]
  have hX1ne2 : hXc.extension χ₁ ≠ hXc.extension χ₂ := by
    intro heq; rw [heq, hX2norm] at hX12; exact one_ne_zero hX12
  -- integer coefficients `c₁ = ⟨X,χ₁^{τ₂}⟩`, `c₂ = ⟨X,χ₂^{τ₂}⟩`.
  obtain ⟨c₁, hc₁⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX1Z
  obtain ⟨c₂, hc₂⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX2Z
  -- the step-5 relation `c₂ − c₁ = −1`.
  have hrel := hyp.inner_extension_Xset_sub_eq_neg_one_general hF cX cY
    hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [← hXc_def, ← hX_def, hc₁, hc₂] at hrel
  have hrelℤ : c₂ - c₁ = -1 := by exact_mod_cast hrel
  -- Bessel `c₁² + c₂² ≤ ‖X‖² = 1` via positive-definiteness of the projection residual
  -- `X − c₁·χ₁^{τ₂} − c₂·χ₂^{τ₂}`.
  have hAX : ClassFunction.inner (hXc.extension χ₁) X = (c₁ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₁), hc₁, star_intCast]
  have hBX : ClassFunction.inner (hXc.extension χ₂) X = (c₂ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₂), hc₂, star_intCast]
  have hX21 : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₁) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ₁) (hXc.extension χ₂), hX12,
      star_zero]
  have hww : ClassFunction.inner
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      = ((1 - (c₁ ^ 2 + c₂ ^ 2) : ℤ) : ℂ) := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hXnorm, hc₁, hc₂, hAX, hBX, hX1norm, hX2norm, hX12, hX21, star_intCast]
    push_cast; ring
  have hbℤ : c₁ ^ 2 + c₂ ^ 2 ≤ 1 := by
    have hnn := OddOrder.RepresentationTheory.inner_self_re_nonneg
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
    rw [hww, Complex.intCast_re] at hnn
    have hb : (0 : ℤ) ≤ 1 - (c₁ ^ 2 + c₂ ^ 2) := by exact_mod_cast hnn
    linarith
  -- positive-definiteness: `⟨w₁,w₁⟩=⟨w₂,w₂⟩=⟨w₁,w₂⟩=1 ⟹ w₁=w₂`.
  have heq : ∀ w₁ w₂ : ClassFunction G ℂ, ClassFunction.inner w₁ w₁ = 1 →
      ClassFunction.inner w₂ w₂ = 1 → ClassFunction.inner w₁ w₂ = 1 → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂ h₁₂
    have hsub : ClassFunction.inner (w₁ - w₂) (w₁ - w₂) = 0 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h₁, h₂, h₁₂,
        OddOrder.RepresentationTheory.inner_conj_symm w₁ w₂, h₁₂, star_one]
      ring
    have hz : w₁ - w₂ = 0 := OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero
      (by rw [hsub, Complex.zero_re])
    exact sub_eq_zero.mp hz
  -- the integer dichotomy `(c₁,c₂) = (1,0) ∨ (0,−1)` from `c₂ = c₁−1` and `c₁²+c₂² ≤ 1`.
  have hc2eq : c₂ = c₁ - 1 := by omega
  rw [hc2eq] at hbℤ
  obtain ⟨hb0, hb1⟩ : 0 ≤ c₁ ∧ c₁ ≤ 1 := by
    constructor <;> nlinarith [hbℤ, sq_nonneg c₁, sq_nonneg (c₁ - 1)]
  interval_cases c₁
  · -- `c₁ = 0`, `c₂ = −1` ⟹ `X = −χ₂^{τ₂}`.
    right
    have hc₂m : c₂ = -1 := by omega
    subst hc₂m
    refine heq X (-hXc.extension χ₂) hXnorm ?_ ?_
    · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, hX2norm]; ring
    · rw [ClassFunction.inner_neg_right, hc₂]; norm_num
  · -- `c₁ = 1`, `c₂ = 0` ⟹ `X = χ₁^{τ₂}`.
    left
    refine heq X (hXc.extension χ₁) hXnorm hX1norm ?_
    rw [hc₁]; norm_num

open scoped Classical in
/-- **(6.8.1) step-5 dichotomy `X = χ₁^{τ₂} ∨ X = −χ₂^{τ₂}`**, case (A) / c2 mirror of
`extension_eq_or_eq_neg_general`.  The good-case structure/relation/`X`-irreducibility inputs use
their case-(A) counterparts (`orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA`,
`inner_extension_Xset_sub_eq_neg_one_general_c2_caseA`,
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem extension_eq_or_eq_neg_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁)
      = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = cX.extension χ₁
      ∨ hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ = -cX.extension χ₂
      := by
  classical
  set hXc := cX with hXc_def
  set X := hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁ with hX_def
  -- good-case structure: `‖X‖² = 1`, `X ∈ ZIrr` (fold the unfolded `X` from the good-case lemma).
  obtain ⟨_, hXnorm, hXZ⟩ := hyp.orthogonal_normOne_tau_scaledDiff_add_extension_general_c2_caseA
    hK hW1 hA cY hη₁ hχ₁ ha hgood
  rw [← hX_def] at hXnorm hXZ
  -- `X`-image orthonormality, ZIrr membership, distinctness.
  have hX1Z : hXc.extension χ₁ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₁ (Submodule.subset_span hχ₁)
  have hX2Z : hXc.extension χ₂ ∈ ZIrr G := hXc.extension_mem_ZIrr χ₂ (Submodule.subset_span hχ₂)
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (hXc.extension ψ) (hXc.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [hXc.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ'⟩ : IrreducibleCharacter
          ↥L)
    simpa using h
  have hX1norm : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₁) = 1 := by
    rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have hX2norm : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₂) = 1 := by
    rw [hXon χ₂ χ₂ hχ₂ hχ₂, if_pos rfl]
  have hX12 : ClassFunction.inner (hXc.extension χ₁) (hXc.extension χ₂) = 0 := by
    rw [hXon χ₁ χ₂ hχ₁ hχ₂, if_neg (Ne.symm hne)]
  have hX1ne2 : hXc.extension χ₁ ≠ hXc.extension χ₂ := by
    intro heq; rw [heq, hX2norm] at hX12; exact one_ne_zero hX12
  -- integer coefficients `c₁ = ⟨X,χ₁^{τ₂}⟩`, `c₂ = ⟨X,χ₂^{τ₂}⟩`.
  obtain ⟨c₁, hc₁⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX1Z
  obtain ⟨c₂, hc₂⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hXZ hX2Z
  -- the step-5 relation `c₂ − c₁ = −1`.
  have hrel := hyp.inner_extension_Xset_sub_eq_neg_one_general_c2_caseA hK hW1 hA cX cY
    hη₁ hχ₁ hχ₂ hne ha hdeg2
  rw [← hXc_def, ← hX_def, hc₁, hc₂] at hrel
  have hrelℤ : c₂ - c₁ = -1 := by exact_mod_cast hrel
  -- Bessel `c₁² + c₂² ≤ ‖X‖² = 1` via positive-definiteness of the projection residual
  -- `X − c₁·χ₁^{τ₂} − c₂·χ₂^{τ₂}`.
  have hAX : ClassFunction.inner (hXc.extension χ₁) X = (c₁ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₁), hc₁, star_intCast]
  have hBX : ClassFunction.inner (hXc.extension χ₂) X = (c₂ : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (hXc.extension χ₂), hc₂, star_intCast]
  have hX21 : ClassFunction.inner (hXc.extension χ₂) (hXc.extension χ₁) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hXc.extension χ₁) (hXc.extension χ₂), hX12,
      star_zero]
  have hww : ClassFunction.inner
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
      = ((1 - (c₁ ^ 2 + c₂ ^ 2) : ℤ) : ℂ) := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hXnorm, hc₁, hc₂, hAX, hBX, hX1norm, hX2norm, hX12, hX21, star_intCast]
    push_cast; ring
  have hbℤ : c₁ ^ 2 + c₂ ^ 2 ≤ 1 := by
    have hnn := OddOrder.RepresentationTheory.inner_self_re_nonneg
      (X - (c₁ : ℂ) • hXc.extension χ₁ - (c₂ : ℂ) • hXc.extension χ₂)
    rw [hww, Complex.intCast_re] at hnn
    have hb : (0 : ℤ) ≤ 1 - (c₁ ^ 2 + c₂ ^ 2) := by exact_mod_cast hnn
    linarith
  -- positive-definiteness: `⟨w₁,w₁⟩=⟨w₂,w₂⟩=⟨w₁,w₂⟩=1 ⟹ w₁=w₂`.
  have heq : ∀ w₁ w₂ : ClassFunction G ℂ, ClassFunction.inner w₁ w₁ = 1 →
      ClassFunction.inner w₂ w₂ = 1 → ClassFunction.inner w₁ w₂ = 1 → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂ h₁₂
    have hsub : ClassFunction.inner (w₁ - w₂) (w₁ - w₂) = 0 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h₁, h₂, h₁₂,
        OddOrder.RepresentationTheory.inner_conj_symm w₁ w₂, h₁₂, star_one]
      ring
    have hz : w₁ - w₂ = 0 := OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero
      (by rw [hsub, Complex.zero_re])
    exact sub_eq_zero.mp hz
  -- the integer dichotomy `(c₁,c₂) = (1,0) ∨ (0,−1)` from `c₂ = c₁−1` and `c₁²+c₂² ≤ 1`.
  have hc2eq : c₂ = c₁ - 1 := by omega
  rw [hc2eq] at hbℤ
  obtain ⟨hb0, hb1⟩ : 0 ≤ c₁ ∧ c₁ ≤ 1 := by
    constructor <;> nlinarith [hbℤ, sq_nonneg c₁, sq_nonneg (c₁ - 1)]
  interval_cases c₁
  · -- `c₁ = 0`, `c₂ = −1` ⟹ `X = −χ₂^{τ₂}`.
    right
    have hc₂m : c₂ = -1 := by omega
    subst hc₂m
    refine heq X (-hXc.extension χ₂) hXnorm ?_ ?_
    · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, hX2norm]; ring
    · rw [ClassFunction.inner_neg_right, hc₂]; norm_num
  · -- `c₁ = 1`, `c₂ = 0` ⟹ `X = χ₁^{τ₂}`.
    left
    refine heq X (hXc.extension χ₁) hXnorm hX1norm ?_
    rw [hc₁]; norm_num

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08


