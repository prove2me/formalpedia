-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCore
-- name    : OddOrder_Peterfalvi_S08_CoherenceCore
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:54:06.934786+00:00
-- url     : https://prove2.me/theorems/f4e1e841-8d47-4a59-b256-bb9bea230598
-- title:
--   Peterfalvi §8: Sibley–Dade coherence core (tail), the (6.8.1) crux and capstone
-- statement:
--   The final part of the Peterfalvi §8 coherence core, assembling the (6.8.1) crux and the $X(Z_c)\cup Y$ coherence capstone.
--
--   Main results: `crux_general_of_higher_anchor` (the (6.8.1) crux with any third anchor), `exists_Ycoherence_hgood_of_frobenius` (a $Y$-coherence witness in the good case), `exists_Xcoherence_crux_of_card_two_of_frobenius` (the $|X(Z_c)|=2$ edge) and the capstone `coherentXunionYset_centralCommutator_diagonal_general`, with case-(A)/c2 mirrors.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CoherenceCore.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CoherenceCore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_RestrictExtensionDvd
import Definitions.Def_OddOrder_Peterfalvi_S08_SibleyCoherenceLemmas

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **(6.8.1) crux, general witnesses + ANY third anchor (`|X(Zc)| ≥ 3`)** — closes the
`|xBaseBlock| = 2 ∧ |X(Zc)| ≥ 3` gap that the equal-degree `crux_of_third_anchor_general` (which
needs a *third equal-degree* anchor, i.e. `|xBaseBlock| ≥ 3`) cannot reach.  Given the good case
`⟨(χ₁−aη₁)^τ, cY η₁⟩ = −a`, the dichotomy `X = cX χ₁ ∨ X = −cX χ₂` (equal-degree `χ₂`); the right
disjunct is excluded by ANY third `X`-member `χ₃` (any degree) via the degree-ratio relation
`⟨X, cX χ₃⟩ − d₃·⟨X, cX χ₁⟩ = −d₃` (`inner_extension_Xset_scaledSub_eq_neg_general`): under
`X = −cX χ₂` both inner products vanish (distinct `X`-images), giving `0 = −d₃`, impossible since
`d₃ > 0`.  Hence the crux `(χ₁−aη₁)^τ = cX χ₁ − a·cY η₁`. -/
theorem crux_general_of_higher_anchor
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  obtain ⟨d, hdpos, hd⟩ :=
    hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X hp hHp
      (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hχ₃ hχ₁base
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (cX.extension ψ) (cX.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [cX.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rcases hyp.extension_eq_or_eq_neg_general hF cX cY hη₁ hχ₁X hχ₂ hne₂ ha hdeg2 hgood with h | h
  · exact eq_sub_of_add_eq h
  · exfalso
    have hrel3 := hyp.inner_extension_Xset_scaledSub_eq_neg_general hF cX cY hη₁ hχ₁X hχ₃ hne₃₁
      ha hd
    rw [h, ClassFunction.inner_neg_left, ClassFunction.inner_neg_left,
      hXon χ₂ χ₃ hχ₂ hχ₃, if_neg (Ne.symm hne₃₂), hXon χ₂ χ₁ hχ₂ hχ₁X, if_neg hne₂] at hrel3
    have hd0 : (d : ℂ) = 0 := by linear_combination hrel3
    rw [Nat.cast_eq_zero] at hd0
    omega

open scoped Classical in
/-- **(6.8.1) crux, general witnesses + ANY third anchor**, case (A) / c2 mirror of
`crux_general_of_higher_anchor`.  The dichotomy/relation/`X`-irreducibility inputs use their
case-(A) counterparts (`extension_eq_or_eq_neg_general_c2_caseA`,
`inner_extension_Xset_scaledSub_eq_neg_general_c2_caseA`,
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem crux_general_of_higher_anchor_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ χ₃ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne₂ : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne₃₁ : χ₃ ≠ χ₁) (hne₃₂ : χ₃ ≠ χ₂)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  obtain ⟨d, hdpos, hd⟩ :=
    hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X hp hHp
      (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h) hχ₃ hχ₁base
  have hXon : ∀ ψ ψ', ψ ∈ hyp.Xset hyp.centralCommutator →
      ψ' ∈ hyp.Xset hyp.centralCommutator →
      ClassFunction.inner (cX.extension ψ) (cX.extension ψ') = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    rw [cX.extension_inner_eq ψ ψ' (Submodule.subset_span hψ) (Submodule.subset_span hψ')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ',
          hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rcases hyp.extension_eq_or_eq_neg_general_c2_caseA hK hW1 hA cX cY hη₁ hχ₁X hχ₂ hne₂ ha hdeg2
    hgood with h | h
  · exact eq_sub_of_add_eq h
  · exfalso
    have hrel3 := hyp.inner_extension_Xset_scaledSub_eq_neg_general_c2_caseA hK hW1 hA cX cY hη₁
      hχ₁X hχ₃ hne₃₁ ha hd
    rw [h, ClassFunction.inner_neg_left, ClassFunction.inner_neg_left,
      hXon χ₂ χ₃ hχ₂ hχ₃, if_neg (Ne.symm hne₃₂), hXon χ₂ χ₁ hχ₂ hχ₁X, if_neg hne₂] at hrel3
    have hd0 : (d : ℂ) = 0 := by linear_combination hrel3
    rw [Nat.cast_eq_zero] at hd0
    omega

open scoped Classical in
/-- **(6.8.1) E2: a `Y`-coherence witness in the good case** (the `m = 2` relabel, folded in).
Produces a `Y`-coherence witness `cY` with `⟨(χ₁−aη₁)^τ, cY η₁⟩ = −a` — the `hgood` that the crux
consumes.  Generic `|Y| ≥ 3`: `cY = coherentYset` (good branch of the step-4 dichotomy
`coeff_eq_neg_or_edge_of_frobenius`).  Edge `|Y| = 2`: `coherentYset` may give the bad value `0`;
then `Y = {η₁, η₂}` and the sign-swapped witness `cY'` (`coherentEqualDegree_swap_neg`,
`η₁ ↦ −η₂^{τ₁}`) gives `⟨v, cY' η₁⟩ = −⟨v, coherentYset η₂⟩ = −a`, since
`⟨v, coherentYset η₂⟩ = ⟨v, coherentYset η₁⟩ + a = 0 + a = a` (`inner_tau_scaledDiff_tau_Yset_diff`
+ `extends_on_supported`). -/
theorem exists_Ycoherence_hgood_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ) := by
  classical
  rcases hyp.coeff_eq_neg_or_edge_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha with
    hgood | ⟨hm2, hbad⟩
  · exact ⟨hyp.coherentYset, hgood⟩
  · -- edge `|Y| = 2`: relabel.
    obtain ⟨η₂, hη₂Y, hη₂ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < hyp.Yset.ncard) η₁
    have hpairsub : ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Yset := by
      intro x hx; rcases hx with rfl | rfl
      · exact hη₁
      · exact hη₂Y
    have hYeq : hyp.Yset = ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) :=
      (Set.eq_of_subset_of_ncard_le hpairsub (hm2.le.trans_eq (Set.ncard_pair hη₂ne.symm).symm)
        hyp.Yset_finite).symm
    -- orthonormality of `η₁, η₂` (distinct irreducible `Y`-members).
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have hY1irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
    have hY2irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₂Y
    have horth : ClassFunction.inner η₁ η₂ = 0 := by
      rw [hinner η₁ η₂ hY1irr hY2irr, if_neg (Ne.symm hη₂ne)]
    have hn1 : ClassFunction.inner η₁ η₁ = 1 := by rw [hinner η₁ η₁ hY1irr hY1irr, if_pos rfl]
    have hn2 : ClassFunction.inner η₂ η₂ = 1 := by rw [hinner η₂ η₂ hY2irr hY2irr, if_pos rfl]
    have hdeg : (η₂ : ↥L → ℂ) 1 = (η₁ : ↥L → ℂ) 1 :=
      (hyp.Yset_apply_one hη₂Y).trans (hyp.Yset_apply_one hη₁).symm
    have hdeg0 : (η₁ : ↥L → ℂ) 1 ≠ 0 := by
      rw [hyp.Yset_apply_one hη₁]; exact_mod_cast Nat.card_pos.ne'
    have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
    have hsupp : (η₂ - η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη₂Y) (hyp.Yset_subset_S hη₁) hdeg
    -- transport `coherentYset` to the pair, build the swapped witness, transport back.
    have hcY0map : (hYeq ▸ hyp.coherentYset).extension = hyp.coherentYset.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq hyp.coherentYset
    obtain ⟨cY', hcY'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hYeq ▸ hyp.coherentYset) horth hn1 hn2 hdeg hdeg0 h1A hsupp
    refine ⟨hYeq.symm ▸ cY', ?_⟩
    -- `⟨v, η₂^{τ₁}⟩ = a` from the constancy + the bad value `⟨v, η₁^{τ₁}⟩ = 0`.
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_of_frobenius hF hη₁ hη₂Y hη₂ne hχ₁ ha
    have htaud : hyp.tau (η₂ - η₁)
        = hyp.coherentYset.extension η₂ - hyp.coherentYset.extension η₁ := by
      rw [← hyp.coherentYset.extends_on_supported (η₂ - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη₂Y) (Submodule.subset_span hη₁), hsupp⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hbad, sub_zero] at hconst
    -- assemble: `⟨v, (cY' η₁)⟩ = −⟨v, coherentYset η₂⟩ = −a`.
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq.symm cY', hcY'1, hcY0map,
      ClassFunction.inner_neg_right, hconst]

open scoped Classical in
/-- **(6.8.1) E2: a `Y`-coherence witness in the good case**, case (A) / c2 mirror of
`exists_Ycoherence_hgood_of_frobenius`.  The step-4 dichotomy/constancy inputs use their case-(A)
counterparts (`coeff_eq_neg_or_edge_c2_caseA`, `inner_tau_scaledDiff_tau_Yset_diff_c2_caseA`)
instead of `hF` (cert data `hK`/`hW1`/`hA`); the non-`hF` `coherentEqualDegree_swap_neg` relabel is
copied verbatim. -/
theorem exists_Ycoherence_hgood_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ) := by
  classical
  rcases hyp.coeff_eq_neg_or_edge_c2_caseA hK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁ ha_pos ha with
    hgood | ⟨hm2, hbad⟩
  · exact ⟨hyp.coherentYset, hgood⟩
  · -- edge `|Y| = 2`: relabel.
    obtain ⟨η₂, hη₂Y, hη₂ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < hyp.Yset.ncard) η₁
    have hpairsub : ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Yset := by
      intro x hx; rcases hx with rfl | rfl
      · exact hη₁
      · exact hη₂Y
    have hYeq : hyp.Yset = ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) :=
      (Set.eq_of_subset_of_ncard_le hpairsub (hm2.le.trans_eq (Set.ncard_pair hη₂ne.symm).symm)
        hyp.Yset_finite).symm
    -- orthonormality of `η₁, η₂` (distinct irreducible `Y`-members).
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have hY1irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
    have hY2irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₂Y
    have horth : ClassFunction.inner η₁ η₂ = 0 := by
      rw [hinner η₁ η₂ hY1irr hY2irr, if_neg (Ne.symm hη₂ne)]
    have hn1 : ClassFunction.inner η₁ η₁ = 1 := by rw [hinner η₁ η₁ hY1irr hY1irr, if_pos rfl]
    have hn2 : ClassFunction.inner η₂ η₂ = 1 := by rw [hinner η₂ η₂ hY2irr hY2irr, if_pos rfl]
    have hdeg : (η₂ : ↥L → ℂ) 1 = (η₁ : ↥L → ℂ) 1 :=
      (hyp.Yset_apply_one hη₂Y).trans (hyp.Yset_apply_one hη₁).symm
    have hdeg0 : (η₁ : ↥L → ℂ) 1 ≠ 0 := by
      rw [hyp.Yset_apply_one hη₁]; exact_mod_cast Nat.card_pos.ne'
    have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
    have hsupp : (η₂ - η₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη₂Y) (hyp.Yset_subset_S hη₁) hdeg
    -- transport `coherentYset` to the pair, build the swapped witness, transport back.
    have hcY0map : (hYeq ▸ hyp.coherentYset).extension = hyp.coherentYset.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq hyp.coherentYset
    obtain ⟨cY', hcY'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hYeq ▸ hyp.coherentYset) horth hn1 hn2 hdeg hdeg0 h1A hsupp
    refine ⟨hYeq.symm ▸ cY', ?_⟩
    -- `⟨v, η₂^{τ₁}⟩ = a` from the constancy + the bad value `⟨v, η₁^{τ₁}⟩ = 0`.
    have hconst := hyp.inner_tau_scaledDiff_tau_Yset_diff_c2_caseA hK hW1 hA hη₁ hη₂Y hη₂ne hχ₁ ha
    have htaud : hyp.tau (η₂ - η₁)
        = hyp.coherentYset.extension η₂ - hyp.coherentYset.extension η₁ := by
      rw [← hyp.coherentYset.extends_on_supported (η₂ - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη₂Y) (Submodule.subset_span hη₁), hsupp⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hbad, sub_zero] at hconst
    -- assemble: `⟨v, (cY' η₁)⟩ = −⟨v, coherentYset η₂⟩ = −a`.
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq.symm cY', hcY'1, hcY0map,
      ClassFunction.inner_neg_right, hconst]

open scoped Classical in
/-- **(6.8.1) E3: `X`-coherence witness + crux in the `|X(Zc)| = 2` edge** (the `n = 2` relabel).
When `X(Zc) = {χ₁, χ₂}` (a conjugate pair, equal degree), the step-5 dichotomy
`X = cX₀ χ₁ ∨ X = −cX₀ χ₂` (`extension_eq_or_eq_neg_general` at the fixed `cX₀`) has no third anchor
to exclude the right disjunct; instead, the right disjunct is *absorbed* by the sign-swapped witness
`cX'` (`coherentEqualDegree_swap_neg`, `χ₁ ↦ −χ₂^{τ₂}`, valid because `|X| = 2` is the whole set):
`cX' χ₁ = −cX₀ χ₂ = X`, giving the crux `(χ₁−aη₁)^τ = cX' χ₁ − a·cY η₁`. Left disjunct uses
`cX = cX₀`
directly.  Produces a witness + crux for *some* `cX`. -/
theorem exists_Xcoherence_crux_of_card_two_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hXeq : hyp.Xset hyp.centralCommutator = ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)))
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    ∃ cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  set cX0 := hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp with hcX0def
  rcases hyp.extension_eq_or_eq_neg_general hF cX0 cY hη₁ hχ₁ hχ₂ hne ha hdeg2 hgood with h | h
  · -- left disjunct `X = cX₀ χ₁` ⟹ crux for `cX₀`.
    exact ⟨cX0, eq_sub_of_add_eq h⟩
  · -- right disjunct `X = −cX₀ χ₂` ⟹ relabel `cX' χ₁ = −cX₀ χ₂`.
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have hh := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hh
      rw [hh]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have hX1irr := hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁
    have hX2irr := hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₂
    have horth : ClassFunction.inner χ₁ χ₂ = 0 := by
      rw [hinner χ₁ χ₂ hX1irr hX2irr, if_neg (Ne.symm hne)]
    have hn1 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hinner χ₁ χ₁ hX1irr hX1irr, if_pos rfl]
    have hn2 : ClassFunction.inner χ₂ χ₂ = 1 := by rw [hinner χ₂ χ₂ hX2irr hX2irr, if_pos rfl]
    have hdeg0 : (χ₁ : ↥L → ℂ) 1 ≠ 0 := by
      obtain ⟨d, hdpos, hdeq⟩ :=
        irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ₁, hX1irr⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hdeq
      rw [hdeq]; exact_mod_cast hdpos.ne'
    have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
    have hsupp : (χ₂ - χ₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
    have hcX0map : (hXeq ▸ cX0).extension = cX0.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq cX0
    obtain ⟨cX', hcX'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hXeq ▸ cX0) horth hn1 hn2 hdeg2 hdeg0 h1A hsupp
    refine ⟨hXeq.symm ▸ cX', ?_⟩
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq.symm cX', hcX'1, hcX0map]
    exact eq_sub_of_add_eq h

open scoped Classical in
/-- **(6.8.1) E3: `X`-coherence witness + crux in the `|X(Zc)| = 2` edge**, case (A) / c2 mirror of
`exists_Xcoherence_crux_of_card_two_of_frobenius`. The fixed
`X`-coherence/dichotomy/`X`-irreducibility
inputs use their case-(A) counterparts (`Xset_centralCommutator_isCoherent_of_c2_caseA`,
`extension_eq_or_eq_neg_general_c2_caseA`, `isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of
`hF` (cert data `hK`/`hW1`/`hA`); the non-`hF` `coherentEqualDegree_swap_neg` relabel is copied
verbatim. -/
theorem exists_Xcoherence_crux_of_card_two_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₂ : χ₂ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₂ ≠ χ₁) (hdeg2 : χ₂ 1 = χ₁ 1)
    (hXeq : hyp.Xset hyp.centralCommutator = ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)))
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hgood : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (cY.extension η₁) = -(a : ℂ)) :
    ∃ cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁ := by
  classical
  set cX0 := hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp
    with hcX0def
  rcases hyp.extension_eq_or_eq_neg_general_c2_caseA hK hW1 hA cX0 cY hη₁ hχ₁ hχ₂ hne ha hdeg2
    hgood with h | h
  · -- left disjunct `X = cX₀ χ₁` ⟹ crux for `cX₀`.
    exact ⟨cX0, eq_sub_of_add_eq h⟩
  · -- right disjunct `X = −cX₀ χ₂` ⟹ relabel `cX' χ₁ = −cX₀ χ₂`.
    have hinner : ∀ φ ψ : ClassFunction ↥L ℂ, IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
        ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have hh := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hh
      rw [hh]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have hX1irr := hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁
    have hX2irr := hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₂
    have horth : ClassFunction.inner χ₁ χ₂ = 0 := by
      rw [hinner χ₁ χ₂ hX1irr hX2irr, if_neg (Ne.symm hne)]
    have hn1 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hinner χ₁ χ₁ hX1irr hX1irr, if_pos rfl]
    have hn2 : ClassFunction.inner χ₂ χ₂ = 1 := by rw [hinner χ₂ χ₂ hX2irr hX2irr, if_pos rfl]
    have hdeg0 : (χ₁ : ↥L → ℂ) 1 ≠ 0 := by
      obtain ⟨d, hdpos, hdeq⟩ :=
        irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ₁, hX1irr⟩ : IrreducibleCharacter ↥L)
      simp only [IrreducibleCharacter.coe_mk] at hdeq
      rw [hdeq]; exact_mod_cast hdpos.ne'
    have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
    have hsupp : (χ₂ - χ₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₂) (hyp.Xset_subset_S hχ₁) hdeg2
    have hcX0map : (hXeq ▸ cX0).extension = cX0.extension :=
      OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq cX0
    obtain ⟨cX', hcX'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
      (hXeq ▸ cX0) horth hn1 hn2 hdeg2 hdeg0 h1A hsupp
    refine ⟨hXeq.symm ▸ cX', ?_⟩
    rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hXeq.symm cX', hcX'1, hcX0map]
    exact eq_sub_of_add_eq h

/-- **(6.8.1) capstone `X(Zc) ∪ Y` coherence from a witness-level crux** (general form).  Given
arbitrary coherence witnesses `cX` (for `X(Zc)`), `cY` (for `Y`), a base-block anchor `χ₁` with
`χ₁(1) = a·|W₁|`, an `η₁ ∈ Y`, and the **crux** `(χ₁−aη₁)^τ = cX χ₁ − a·cY η₁` (whichever way it is
established — the generic `n,m ≥ 3` argument or the `m=2`/`n=2` relabel), the union `X(Zc) ∪ Y` is
coherent.  `ν` is the `τ₃` glue of `cX`/`cY`; `hmixed = himg_ortho_general`, `hDτ = hcrux`,
`hgen = hgen_withDiagonal`.  This is the common assembly shared by the generic case and both edge
cases (which differ only in how `hcrux` is produced for the chosen witnesses). -/
noncomputable def coherentXunionYset_centralCommutator_diagonal_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hcrux : hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hXY : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner x y = 0 := fun x hx y hy => by
    rw [hinner x y (hXirr x hx) (hYirr y hy),
      if_neg (by intro h; exact Set.disjoint_left.mp hdisj hx (h ▸ hy))]
  have hglue :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthonormal
      (hyp.Xset_finite hyp.centralCommutator) hyp.Yset_finite
      (fun x hx x' hx' => hinner x x' (hXirr x hx) (hXirr x' hx'))
      (fun y hy y' hy' => hinner y y' (hYirr y hy) (hYirr y' hy')) hXY
      cX.extension cY.extension
  refine hyp.coherentXunionYset_centralCommutator_of_glued_withDiagonal_general
    hF cX cY hglue.choose hglue.choose_spec.1 hglue.choose_spec.2 (fun x hx y hy => ?_)
    {χ₁ - a • η₁} (fun d hd => ?_)
    (hyp.hgen_withDiagonal_of_frobenius hF hp hHp hη₁ hχ₁base ha)
  · -- `hmixed`: `⟨ν x, ν y⟩ = ⟨x, y⟩` (both `0`).
    rw [hglue.choose_spec.1 x hx, hglue.choose_spec.2 y hy,
      hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF cX cY hx hy, hXY x hx y hy]
  · -- `hDτ`: `ν(χ₁−aη₁) = (χ₁−aη₁)^τ` = the crux.
    rw [Set.mem_singleton_iff] at hd
    subst hd
    rw [map_sub, map_nsmul, hglue.choose_spec.1 χ₁ hχ₁X, hglue.choose_spec.2 η₁ hη₁,
      ← Nat.cast_smul_eq_nsmul ℂ a (cY.extension η₁)]
    exact hcrux.symm

/-- **(6.8.1) capstone `X(Zc) ∪ Y` coherence from a witness-level crux**, case (A) / c2 mirror of
`coherentXunionYset_centralCommutator_diagonal_general`.  The glue/`X ⊥ Y`/`hgen`/`X`-irreducibility
inputs use their case-(A) counterparts
(`coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_c2_caseA`,
`inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA`,
`hgen_withDiagonal_c2_caseA`,
`isIrreducibleCharacter_of_mem_Xset_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
noncomputable def coherentXunionYset_centralCommutator_diagonal_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ))
    (hcrux : hyp.tau (χ₁ - a • η₁) = cX.extension χ₁ - (a : ℂ) • cY.extension η₁) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hXY : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner x y = 0 := fun x hx y hy => by
    rw [hinner x y (hXirr x hx) (hYirr y hy),
      if_neg (by intro h; exact Set.disjoint_left.mp hdisj hx (h ▸ hy))]
  have hglue :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthonormal
      (hyp.Xset_finite hyp.centralCommutator) hyp.Yset_finite
      (fun x hx x' hx' => hinner x x' (hXirr x hx) (hXirr x' hx'))
      (fun y hy y' hy' => hinner y y' (hYirr y hy) (hYirr y' hy')) hXY
      cX.extension cY.extension
  refine hyp.coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_c2_caseA
    hK hW1 hA cX cY hglue.choose hglue.choose_spec.1 hglue.choose_spec.2 (fun x hx y hy => ?_)
    {χ₁ - a • η₁} (fun d hd => ?_)
    (hyp.hgen_withDiagonal_c2_caseA hK hW1 hA hp hHp hη₁ hχ₁base ha)
  · -- `hmixed`: `⟨ν x, ν y⟩ = ⟨x, y⟩` (both `0`).
    rw [hglue.choose_spec.1 x hx, hglue.choose_spec.2 y hy,
      hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA hK hW1 hA cX cY hx
        hy,
      hXY x hx y hy]
  · -- `hDτ`: `ν(χ₁−aη₁) = (χ₁−aη₁)^τ` = the crux.
    rw [Set.mem_singleton_iff] at hd
    subst hd
    rw [map_sub, map_nsmul, hglue.choose_spec.1 χ₁ hχ₁X, hglue.choose_spec.2 η₁ hη₁,
      ← Nat.cast_smul_eq_nsmul ℂ a (cY.extension η₁)]
    exact hcrux.symm

open scoped Classical in
/-- **(6.8) capstone, case (A) (Frobenius): `S` is coherent — UNCONDITIONAL** (no `3 ≤` cardinality
hypotheses; the `m = 2` / `n = 2` edge relabels are handled internally).  This is the full case-(A)
result: only `2 ≤ |xBaseBlock|` (`two_le_xBaseBlock_ncard`) and `2 ≤ |Y|` (`two_le_Yset_ncard`),
both unconditionally available, are used.  E2 (`exists_Ycoherence_hgood_of_frobenius`) supplies the
`Y`-witness + good case (the `m = 2` relabel).  The `X`-side splits on `|X(Zc)|`: `≥ 3` uses the
degree-ratio crux E1 (`crux_general_of_higher_anchor`) at the fixed `X`-witness; `= 2` uses the
relabel crux E3 (`exists_Xcoherence_crux_of_card_two_of_frobenius`).  Either way the crux feeds the
shared assembly `coherentXunionYset_centralCommutator_diagonal_general`, giving `X(Zc) ∪ Y`
coherent,
and the (6.8.3) extension `false_of_coherentXunionYset_of_not_coherentS` lifts it to `S`. -/
theorem nonempty_coherent_S_caseA_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  classical
  by_contra hncoh
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty :=
    hyp.Xset_centralCommutator_nonempty hF hHnonab
  have hXfin : (hyp.Xset hyp.centralCommutator).Finite := hyp.Xset_finite hyp.centralCommutator
  have h2X : 2 ≤ (hyp.xBaseBlock hyp.centralCommutator).ncard :=
    hyp.two_le_xBaseBlock_ncard hF hyp.centralCommutator_le hXne
  -- two distinct base-block anchors.
  obtain ⟨χ₁, hχ₁base, χ₂, hχ₂base, hne⟩ : ∃ a ∈ hyp.xBaseBlock hyp.centralCommutator,
      ∃ b ∈ hyp.xBaseBlock hyp.centralCommutator, b ≠ a := by
    obtain ⟨a, ha⟩ : (hyp.xBaseBlock hyp.centralCommutator).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard
      (s := hyp.xBaseBlock hyp.centralCommutator) (by omega) a
    exact ⟨a, ha, b, hb, hba⟩
  have hχ₁X := hyp.xBaseBlock_subset _ hχ₁base
  have hχ₂X := hyp.xBaseBlock_subset _ hχ₂base
  -- `η₁ ∈ Y` (degree `|W₁|`) and the degree ratio `a`.
  obtain ⟨η₁, hη₁⟩ := hyp.Yset_nonempty
  obtain ⟨a, ha_pos, ha⟩ := hyp.sMember_charValue_one_eq_mul_anchor (hyp.Xset_subset_S hχ₁X)
    (hyp.Yset_apply_one hη₁)
  rw [hyp.Yset_apply_one hη₁] at ha
  -- base block equal-degree.
  have hdegeq : ∀ χ' ∈ hyp.xBaseBlock hyp.centralCommutator, χ' 1 = χ₁ 1 := by
    intro χ' hχ'
    have hre := hyp.xBaseBlock_degree_re_eq hχ' hχ₁base
    rw [OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hre
    obtain ⟨d', _, hd'⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ', hXirr χ' (hyp.xBaseBlock_subset _ hχ')⟩ : IrreducibleCharacter ↥L)
    obtain ⟨d₁, _, hd₁⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hXirr χ₁ hχ₁X⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd' hd₁
    rw [hd', hd₁] at hre ⊢
    exact_mod_cast hre
  have hdeg2 : χ₂ 1 = χ₁ 1 := hdegeq χ₂ hχ₂base
  -- E2: the `Y`-witness with the good case (m = 2 relabel folded in).
  obtain ⟨cY, hgood⟩ :=
    hyp.exists_Ycoherence_hgood_of_frobenius hF hHnonab hp hp3 hHp hη₁ hχ₁X ha_pos ha
  -- build `X(Zc) ∪ Y` coherent, splitting on `|X(Zc)|`.
  have hXYcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    by_cases h3X : 3 ≤ (hyp.Xset hyp.centralCommutator).ncard
    · -- `|X(Zc)| ≥ 3`: a third `X`-member of ANY degree (E1, degree-ratio exclusion).
      have hex : ∃ c ∈ hyp.Xset hyp.centralCommutator, c ≠ χ₁ ∧ c ≠ χ₂ := by
        have hpair : ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Xset hyp.centralCommutator := by
          intro x hx; rcases hx with rfl | rfl
          · exact hχ₁X
          · exact hχ₂X
        have hdc : (hyp.Xset hyp.centralCommutator \ {χ₁, χ₂}).ncard
            = (hyp.Xset hyp.centralCommutator).ncard - 2 := by
          rw [Set.ncard_sdiff hpair, Set.ncard_pair (Ne.symm hne)]
        have hcne : (hyp.Xset hyp.centralCommutator \ {χ₁, χ₂}).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]; intro he; rw [he, Set.ncard_empty] at hdc; omega
        obtain ⟨c, hcs, hcnp⟩ := hcne
        rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcnp
        exact ⟨c, hcs, hcnp.1, hcnp.2⟩
      have cX0 := hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp
      exact hyp.coherentXunionYset_centralCommutator_diagonal_general hF hp hHp cX0 cY hη₁
        hχ₁base ha (hyp.crux_general_of_higher_anchor hF hp hHp cX0 cY hη₁ hχ₁base hχ₂X hne hdeg2
          hex.choose_spec.1 hex.choose_spec.2.1 hex.choose_spec.2.2 ha hgood)
    · -- `|X(Zc)| = 2`: relabel (E3).
      have h2Xle : 2 ≤ (hyp.Xset hyp.centralCommutator).ncard :=
        le_trans h2X (Set.ncard_le_ncard (hyp.xBaseBlock_subset _) hXfin)
      have h2Xeq : (hyp.Xset hyp.centralCommutator).ncard = 2 := by omega
      have hpairsub : ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Xset hyp.centralCommutator := by
        intro x hx; rcases hx with rfl | rfl
        · exact hχ₁X
        · exact hχ₂X
      have hXeq : hyp.Xset hyp.centralCommutator = ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) :=
        (Set.eq_of_subset_of_ncard_le hpairsub
          (h2Xeq.le.trans_eq (Set.ncard_pair (Ne.symm hne)).symm) hXfin).symm
      have hexX := hyp.exists_Xcoherence_crux_of_card_two_of_frobenius hF hHnonab hp hp3 hHp
        cY hη₁ hχ₁X hχ₂X hne hdeg2 hXeq ha hgood
      exact hyp.coherentXunionYset_centralCommutator_diagonal_general hF hp hHp hexX.choose cY hη₁
        hχ₁base ha hexX.choose_spec
  exact hyp.false_of_coherentXunionYset_of_not_coherentS hF hHnonab ⟨hXYcoh⟩ hncoh

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08


