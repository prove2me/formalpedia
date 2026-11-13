-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_SibleyCoherenceLemmas
-- name    : OddOrder_Peterfalvi_S08_SibleyCoherenceLemmas
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:50:41.006312+00:00
-- url     : https://prove2.me/theorems/32707d14-2fca-4965-ba4f-301650dfc33e
-- title:
--   Peterfalvi §8: Sibley–Dade coherence, opening lemma layer
-- statement:
--   The opening lemma layer of the Sibley–Dade coherence argument in Peterfalvi §8, (6.8.1). The bundle consists of lemmas only.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_SibleyCoherenceLemmas.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_SibleyCoherenceLemmas.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_RestrictExtensionDvd

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **(6.8.1) `hgen'` — the diagonal-aware generation hypothesis** (mmd 04.8 L176).  Every supported
`X(Zc) ∪ Y`-combination lies in the span of the supported `X(Zc)`-combinations, the supported
`Y`-combinations, and the single cross-diagonal `χ₁ − a·η₁`:
`ℤ[X(Zc) ∪ Y, A] ⊆ span(ℤ[X(Zc), A] ∪ ℤ[Y, A] ∪ {χ₁ − a·η₁})`.

For `φ = φ_X + φ_Y` (`X, Y` disjoint, `Submodule.span_union`), the degree-ratio integrality
(`exists_charValue_one_eq_mul_xBaseBlock_anchor`) gives `s ∈ ℤ` with `φ_X(1) = s·χ₁(1)` (span
induction); then `φ = (φ_X − s·χ₁) + (φ_Y + s·(a·η₁)) + s·(χ₁ − a·η₁)`, where the first two pieces
are degree-`0` (`φ(1) = 0` from support) hence supported
(`zSpan_S_support_subset_of_apply_one_eq_zero`) and the last is a multiple of the diagonal.  This is
the `hgen` field of `coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius` with
`D = {χ₁ − a·η₁}`. -/
theorem hgen_withDiagonal_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
      Submodule.span ℤ
        (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        {χ₁ - a • η₁}) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  intro φ hφ
  obtain ⟨hφspan, hφsupp⟩ := hφ
  -- `φ(1) = 0`: `1 ∉ A = H^#`.
  have h1 : φ 1 = 0 := by
    by_contra h
    have hmem := hφsupp (ClassFunction.mem_support.mpr h)
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
    simp only [sharpImage, Set.mem_sdiff, Set.mem_singleton_iff] at hmem
    exact hmem.2 (by simp)
  -- split `φ = φ_X + φ_Y`.
  rw [OddOrder.Peterfalvi.S07.zSpan, Submodule.span_union] at hφspan
  obtain ⟨φX, hφX, φY, hφY, hsum⟩ := Submodule.mem_sup.mp hφspan
  -- the integer `s` with `φ_X(1) = s·χ₁(1)` (span induction + degree-ratio integrality).
  have hsX : ∀ ψ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator),
      ∃ s : ℤ, ψ 1 = (s : ℂ) * χ₁ 1 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨d, -, hd⟩ := hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X
          hp hHp (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hx hχ₁base
        exact ⟨d, by rw [hd]; push_cast; ring⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
        exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
    | smul c x _ hx =>
        obtain ⟨sx, hsx⟩ := hx
        refine ⟨c * sx, ?_⟩
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring
  obtain ⟨s, hφX1⟩ := hsX φX hφX
  -- `φ_Y(1) = −s·χ₁(1)`.
  have hφY1 : φY 1 = -((s : ℂ) * χ₁ 1) := by
    have haux : φX 1 + φY 1 = 0 := by
      have hc := congrArg (fun ψ : ClassFunction ↥L ℂ => ψ 1) hsum
      simpa [ClassFunction.add_apply, h1] using hc
    linear_combination haux - hφX1
  -- the smul degrees.
  have hsχ₁1 : (s • χ₁ : ClassFunction ↥L ℂ) 1 = (s : ℂ) * χ₁ 1 := by
    rw [← Int.cast_smul_eq_zsmul ℂ s χ₁, ClassFunction.smul_apply]
  have hsaη₁1 : (s • (a • η₁) : ClassFunction ↥L ℂ) 1 = (s : ℂ) * ((a : ℂ) * η₁ 1) := by
    rw [← Int.cast_smul_eq_zsmul ℂ s (a • η₁), ClassFunction.smul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.smul_apply]
  -- the three pieces are degree 0 (for the supported ones) and span-members.
  have hp1deg : (φX - s • χ₁ : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.sub_apply, hφX1, hsχ₁1]; ring
  have hp2deg : (φY + s • (a • η₁) : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.add_apply, hφY1, hsaη₁1, ha, hyp.Yset_apply_one hη₁]; ring
  have hp1span : (φX - s • χ₁) ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) :=
    Submodule.sub_mem _ hφX (Submodule.smul_mem _ s (Submodule.subset_span hχ₁X))
  have hp2span : (φY + s • (a • η₁)) ∈ Submodule.span ℤ hyp.Yset :=
    Submodule.add_mem _ hφY
      (Submodule.smul_mem _ s (nsmul_mem (Submodule.subset_span hη₁) a))
  -- supports via the degree-0 ⟹ supported helper.
  have hp1supp : (φX - s • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Xset_subset_S hp1span) hp1deg
  have hp2supp : (φY + s • (a • η₁)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Yset_subset_S hp2span) hp2deg
  -- assemble `φ = p1 + p2 + p3` (the `s·χ₁`, `s·(a·η₁)` terms cancel).
  have hφeq : φ = (φX - s • χ₁) + (φY + s • (a • η₁)) + s • (χ₁ - a • η₁) := by
    rw [smul_sub, ← hsum]; abel
  rw [hφeq]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_left _ ⟨hp1span, hp1supp⟩))
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_right _ ⟨hp2span, hp2supp⟩))
  · exact Submodule.smul_mem _ s
      (Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _)))

open scoped Classical in
/-- **(6.8.1) `hgen'` — the diagonal-aware generation hypothesis**, case (A) / c2 mirror of
`hgen_withDiagonal_of_frobenius`.  `X`-irreducibility comes from the certain-type input
`isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem hgen_withDiagonal_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁base : χ₁ ∈ hyp.xBaseBlock hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
      Submodule.span ℤ
        (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
        {χ₁ - a • η₁}) := by
  classical
  have hχ₁X : χ₁ ∈ hyp.Xset hyp.centralCommutator := hyp.xBaseBlock_subset _ hχ₁base
  intro φ hφ
  obtain ⟨hφspan, hφsupp⟩ := hφ
  -- `φ(1) = 0`: `1 ∉ A = H^#`.
  have h1 : φ 1 = 0 := by
    by_contra h
    have hmem := hφsupp (ClassFunction.mem_support.mpr h)
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
    simp only [sharpImage, Set.mem_sdiff, Set.mem_singleton_iff] at hmem
    exact hmem.2 (by simp)
  -- split `φ = φ_X + φ_Y`.
  rw [OddOrder.Peterfalvi.S07.zSpan, Submodule.span_union] at hφspan
  obtain ⟨φX, hφX, φY, hφY, hsum⟩ := Submodule.mem_sup.mp hφspan
  -- the integer `s` with `φ_X(1) = s·χ₁(1)` (span induction + degree-ratio integrality).
  have hsX : ∀ ψ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator),
      ∃ s : ℤ, ψ 1 = (s : ℂ) * χ₁ 1 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨d, -, hd⟩ := hyp.exists_charValue_one_eq_mul_xBaseBlock_anchor_of_irreducible_X
          hp hHp (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h) hx hχ₁base
        exact ⟨d, by rw [hd]; push_cast; ring⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨sx, hsx⟩ := hx; obtain ⟨sy, hsy⟩ := hy
        exact ⟨sx + sy, by rw [ClassFunction.add_apply, hsx, hsy]; push_cast; ring⟩
    | smul c x _ hx =>
        obtain ⟨sx, hsx⟩ := hx
        refine ⟨c * sx, ?_⟩
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hsx]; push_cast; ring
  obtain ⟨s, hφX1⟩ := hsX φX hφX
  -- `φ_Y(1) = −s·χ₁(1)`.
  have hφY1 : φY 1 = -((s : ℂ) * χ₁ 1) := by
    have haux : φX 1 + φY 1 = 0 := by
      have hc := congrArg (fun ψ : ClassFunction ↥L ℂ => ψ 1) hsum
      simpa [ClassFunction.add_apply, h1] using hc
    linear_combination haux - hφX1
  -- the smul degrees.
  have hsχ₁1 : (s • χ₁ : ClassFunction ↥L ℂ) 1 = (s : ℂ) * χ₁ 1 := by
    rw [← Int.cast_smul_eq_zsmul ℂ s χ₁, ClassFunction.smul_apply]
  have hsaη₁1 : (s • (a • η₁) : ClassFunction ↥L ℂ) 1 = (s : ℂ) * ((a : ℂ) * η₁ 1) := by
    rw [← Int.cast_smul_eq_zsmul ℂ s (a • η₁), ClassFunction.smul_apply,
      ← Nat.cast_smul_eq_nsmul ℂ a η₁, ClassFunction.smul_apply]
  -- the three pieces are degree 0 (for the supported ones) and span-members.
  have hp1deg : (φX - s • χ₁ : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.sub_apply, hφX1, hsχ₁1]; ring
  have hp2deg : (φY + s • (a • η₁) : ClassFunction ↥L ℂ) 1 = 0 := by
    rw [ClassFunction.add_apply, hφY1, hsaη₁1, ha, hyp.Yset_apply_one hη₁]; ring
  have hp1span : (φX - s • χ₁) ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) :=
    Submodule.sub_mem _ hφX (Submodule.smul_mem _ s (Submodule.subset_span hχ₁X))
  have hp2span : (φY + s • (a • η₁)) ∈ Submodule.span ℤ hyp.Yset :=
    Submodule.add_mem _ hφY
      (Submodule.smul_mem _ s (nsmul_mem (Submodule.subset_span hη₁) a))
  -- supports via the degree-0 ⟹ supported helper.
  have hp1supp : (φX - s • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Xset_subset_S hp1span) hp1deg
  have hp2supp : (φY + s • (a • η₁)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.zSpan_S_support_subset_of_apply_one_eq_zero
      (Submodule.span_mono hyp.Yset_subset_S hp2span) hp2deg
  -- assemble `φ = p1 + p2 + p3` (the `s·χ₁`, `s·(a·η₁)` terms cancel).
  have hφeq : φ = (φX - s • χ₁) + (φY + s • (a • η₁)) + s • (χ₁ - a • η₁) := by
    rw [smul_sub, ← hsum]; abel
  rw [hφeq]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_left _ ⟨hp1span, hp1supp⟩))
  · exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_union_right _ ⟨hp2span, hp2supp⟩))
  · exact Submodule.smul_mem _ s
      (Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton _)))

open scoped Classical in
/-- **(6.8.1) `X`-difference isometry, degree-ratio form** (mmd 04.8 L176: the `n ≥ 3` exclusion
uses
`(χ₃ − d₃χ₁)^τ` for ANY third `X`-member `χ₃`, of any degree).  For `η₁ ∈ Y`, `χ₁ ∈ X(Zc)` with
`χ₁(1) = a·|W₁|`, and a second member `χ₃ ∈ X(Zc)`, `χ₃ ≠ χ₁`, with degree ratio `d` (`χ₃(1) =
d·χ₁(1)`):  `⟨(χ₁−aη₁)^τ, (χ₃−d·χ₁)^τ⟩ = −d`.  Generalizes
`inner_tau_scaledDiff_tau_Xset_diff_of_frobenius` (the `d = 1` equal-degree case `= −1`); the
supported diff `χ₃ − d·χ₁` is degree-`0` (`sMember_scaledDiffSupport_of_charValue_eq`), so the Dade
isometry reduces to the source `⟨χ₁−aη₁, χ₃−d·χ₁⟩ = −d` (`X`-orthonormality + `X ⊥ Y`). -/
theorem inner_tau_scaledDiff_tau_Xset_scaledDiff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₃ - d • χ₁)) = -(d : ℂ) := by
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
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX3 :
      (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade (S := ({χ₁ - a • η₁, χ₃ - d • χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX3)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
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
  have e13 : ClassFunction.inner χ₁ χ₃ = 0 := by rw [hXon χ₁ χ₃ hχ₁ hχ₃, if_neg (Ne.symm hne)]
  have e11 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have ey3 : ClassFunction.inner η₁ χ₃ = 0 := hYXz χ₃ hχ₃
  have ey1 : ClassFunction.inner η₁ χ₁ = 0 := hYXz χ₁ hχ₁
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η₁, ← Nat.cast_smul_eq_nsmul ℂ d χ₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    e13, e11, ey3, ey1, star_natCast]
  ring

open scoped Classical in
/-- **(6.8.1) `X`-difference isometry, degree-ratio form**, case (A) / c2 mirror of
`inner_tau_scaledDiff_tau_Xset_scaledDiff_of_frobenius`.  `X`-irreducibility comes from the
certain-type input `isIrreducibleCharacter_of_mem_Xset_c2_caseA` (cert data `hK`/`hW1`/`hA`)
instead of `hF`. -/
theorem inner_tau_scaledDiff_tau_Xset_scaledDiff_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (hyp.tau (χ₃ - d • χ₁)) = -(d : ℂ) := by
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
  have hdegX : χ₁ 1 = (a : ℂ) * η₁ 1 := by rw [ha, hyp.Yset_apply_one hη₁]
  have hsuppX : (χ₁ - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη₁)
      hdegX
  have hsuppX3 :
      (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade (S := ({χ₁ - a • η₁, χ₃ - d • χ₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppX3)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
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
  have e13 : ClassFunction.inner χ₁ χ₃ = 0 := by rw [hXon χ₁ χ₃ hχ₁ hχ₃, if_neg (Ne.symm hne)]
  have e11 : ClassFunction.inner χ₁ χ₁ = 1 := by rw [hXon χ₁ χ₁ hχ₁ hχ₁, if_pos rfl]
  have ey3 : ClassFunction.inner η₁ χ₃ = 0 := hYXz χ₃ hχ₃
  have ey1 : ClassFunction.inner η₁ χ₁ = 0 := hYXz χ₁ hχ₁
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η₁, ← Nat.cast_smul_eq_nsmul ℂ d χ₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    e13, e11, ey3, ey1, star_natCast]
  ring

open scoped Classical in
/-- **(6.8.1) step-5 relation, degree-ratio form.**  For the good-case element
`X := (χ₁−aη₁)^τ + a·η₁^{τ₁}` and a third `X`-member `χ₃` of degree ratio `d` (`χ₃(1) = d·χ₁(1)`):
`⟨X, χ₃^{τ₂}⟩ − d·⟨X, χ₁^{τ₂}⟩ = −d`.  himg_ortho (`η₁^{τ₁} ⊥ X^{τ₂}`) gives `⟨X,·⟩ = ⟨v,·⟩`; the
`X`-coherence `(χ₃−d·χ₁)^τ = χ₃^{τ₂} − d·χ₁^{τ₂}` and the degree-ratio isometry value
`⟨v, (χ₃−d·χ₁)^τ⟩ = −d` close it.  Generalizes `inner_extension_Xset_sub_eq_neg_one_general`
(the `d = 1` case). -/
theorem inner_extension_Xset_scaledSub_eq_neg_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) (cX.extension χ₃)
      - (d : ℂ) * ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁) = -(d : ℂ) := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (cX.extension χ)
        = ClassFunction.inner v (cX.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF cX cY hχ hη₁
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (cX.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  have hsuppX3 :
      (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hXcoh : hyp.tau (χ₃ - d • χ₁) = cX.extension χ₃ - (d : ℂ) • cX.extension χ₁ := by
    have h := cX.extends_on_supported (χ₃ - d • χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₃)
        (nsmul_mem (Submodule.subset_span hχ₁) d), hsuppX3⟩
    rw [map_sub, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ d (cX.extension χ₁)] at h
    exact h.symm
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_scaledDiff_of_frobenius hF hη₁ hχ₁ hχ₃ hne ha hd
  rw [hXcoh, ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast] at hiso
  rw [hXv χ₃ hχ₃, hXv χ₁ hχ₁]
  exact hiso

open scoped Classical in
/-- **(6.8.1) step-5 relation, degree-ratio form**, case (A) / c2 mirror of
`inner_extension_Xset_scaledSub_eq_neg_general`.  The himg_ortho/isometry inputs use their case-(A)
counterparts (`inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA`,
`inner_tau_scaledDiff_tau_Xset_scaledDiff_c2_caseA`) instead of `hF` (cert data `hK`/`hW1`/`hA`). -/
theorem inner_extension_Xset_scaledSub_eq_neg_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ₁ χ₃ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    (hχ₃ : χ₃ ∈ hyp.Xset hyp.centralCommutator) (hne : χ₃ ≠ χ₁)
    {a d : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) (hd : χ₃ 1 = (d : ℂ) * χ₁ 1) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁) (cX.extension χ₃)
      - (d : ℂ) * ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • cY.extension η₁)
        (cX.extension χ₁) = -(d : ℂ) := by
  classical
  set v := hyp.tau (χ₁ - a • η₁) with hv
  have hXv : ∀ χ ∈ hyp.Xset hyp.centralCommutator,
      ClassFunction.inner (v + (a : ℂ) • cY.extension η₁) (cX.extension χ)
        = ClassFunction.inner v (cX.extension χ) := by
    intro χ hχ
    have h := hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA
      hK hW1 hA cX cY hχ hη₁
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_conj_symm (cX.extension χ)
        (cY.extension η₁), h, star_zero, mul_zero, add_zero]
  have hsuppX3 :
      (χ₃ - d • χ₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₃) (hyp.Xset_subset_S hχ₁) hd
  have hXcoh : hyp.tau (χ₃ - d • χ₁) = cX.extension χ₃ - (d : ℂ) • cX.extension χ₁ := by
    have h := cX.extends_on_supported (χ₃ - d • χ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₃)
        (nsmul_mem (Submodule.subset_span hχ₁) d), hsuppX3⟩
    rw [map_sub, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ d (cX.extension χ₁)] at h
    exact h.symm
  have hiso := hyp.inner_tau_scaledDiff_tau_Xset_scaledDiff_c2_caseA hK hW1 hA hη₁ hχ₁ hχ₃ hne ha hd
  rw [hXcoh, ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast] at hiso
  rw [hXv χ₃ hχ₃, hXv χ₁ hχ₁]
  exact hiso

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08


