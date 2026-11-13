-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceWeighted
-- name    : OddOrder_Peterfalvi_S08_CoherenceWeighted
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:21:36.030456+00:00
-- url     : https://prove2.me/theorems/a98918eb-289f-4914-848a-c935800c6c73
-- title:
--   Peterfalvi §5/§8: the norm-weighted (5.6) coherence-break engine
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §5, Theorem (5.6) under Hypothesis (5.2), in the norm-weighted form needed for the certain-type case (B) of (6.8.3). The earlier $X$-chain machinery assumes orthonormal break characters; this file handles reducible members.
--
--   Main results: `xAdjoinStepW` (the norm-weighted forward adjoin engine for general members), `xAdjoinStepW_k` (reducible break, $\|\chi\|^2\ne1$) and the degree-square bounds `coherentDegreeSqNormBound_of_not_coherentW` and `coherentDegreeSqNormBound_of_not_coherentW_k` (contrapositives of the adjoin engines).
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CoherenceWeighted.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CoherenceWeighted.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_Peterfalvi_S07_RetargetScaled
import Definitions.Def_OddOrder_Peterfalvi_S08_GeneralAdjoinWeighted

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

/-- **The Dade map is an isometry on every supported sublattice** — the `hisom` input of the
general (5.6) engines (`S07.xAdjoinStepW_k_general`, `S07.adjoinPairCoherent_general`), for an
arbitrary ambient family `Samb`.  Pure repackaging of
`dadeIntegralCharacterMap_inner_eq_on_supported_span`: membership in `zSupportedSpan Samb A₀` gives
the `A₀`-support of every generator, which is all that lemma needs (it never looks at `Samb`), so
the Feit–Thompson instantiations may take `Samb = univ`. -/
theorem dade_hisom_of_zSupportedSpan {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (Samb : Set (ClassFunction ↥L ℂ)) :
    ∀ (T : Set (ClassFunction ↥L ℂ)),
      (∀ s ∈ T, s ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) Samb
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) →
      ∀ φ ζ : ClassFunction ↥L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
              (hyp.fullDadeIsometryData) φ)
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
              (hyp.fullDadeIsometryData) ζ)
          = ClassFunction.inner φ ζ :=
  fun _T hT _φ _ζ hφ hζ =>
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
      (fun s hs => (hT s hs).2) hφ hζ

open scoped Classical in
/-- **Norm-weighted (5.6) forward adjoin engine (general members).**

The weighted analogue of `xAdjoinStep` (case A), generalized so the member family `χmem` may
contain **reducible** characters: the per-member ν-aux decompositions `Dmem i` and the family
orthogonalities `hortho_mem`/`htau1Dmem` are taken as **parameters** rather than constructed from
`memberExtensionDecomposition` (which is irreducible-only, requiring `χmem i : IrreducibleCharacter`
via the Dade family `dadeOrthonormalCharacterImageFamilyOfDiff`).

This is exactly the split Peterfalvi (5.6) needs for case (B) of (6.8.3): the break pair `χ, χ̄` and
the anchor `χmem i₁` stay irreducible (norm one), while a non-anchor member may be a reducible
certain-type column `μⱼ` whose orthonormal image family `R(μⱼ)` is supplied by the §6 σ-isometry
(Peterfalvi (5.3.b)).  Each `Dmem i : CharacterPsiDecomposition τ (χmem i) 0` carries that family in
`(Dmem i).imageFamily`, the running extension as `(Dmem i).tau1 = ν` (`htau1Dmem`), and the (5.2.e)
cross-family orthogonality `R(χmem i) ⊥ R(χ)` (`hortho_mem`).

* For an irreducible member, `Dmem i = memberExtensionDecomposition …`, `hortho_mem i =
  dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal …`, `htau1Dmem i = rfl` — recovering the
  case-A instantiation.
* For a reducible certain-type column, `Dmem i` is built via `ofProjection` from the σ-image family
  `R(μⱼ)` ((5.3.b)); this is the remaining §5↔§6 bridge.

The weighting enters only through `mc` (the member norms `‖χmem i‖²`), the weighted orthogonality
`hmemortho`, and the weighted degree bound `hDeg : 2a < ∑ deg² / mc`, all threaded into
`crux1_of_memberFamilyW`. -/
noncomputable def xAdjoinStepW
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χmem i) 0)
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hrealχ
        hdiffsuppχ))
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- Same `Samb = univ` instantiation as `xAdjoinStepW_k`; the break's (5.2.d) family is the
  -- two-element conjugate-pair Dade family (which is why `χ` must be irreducible here).
  refine OddOrder.Peterfalvi.S07.xAdjoinStepW_general (Samb := Set.univ) hS₁ (Set.subset_univ _)
    (dade_hisom_of_zSupportedSpan hyp Set.univ) (χ : ClassFunction ↥L ℂ)
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hrealχ hdiffsuppχ)
    hχχ hχbarχbar hχχbar hχbarχ hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ ?_ hmemS1 mc hmempos hmemortho
    Dmem hortho_mem htau1Dmem ?_ ?_ htau1_memaχ ha1 hDeg hSgen hgen
  -- the scaled member differences lie in the `A₀`-supported part of `ℤ[S₁]`
  · intro i hi
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, hmemdegdiffsupp i hi⟩
    refine Submodule.sub_mem _ (Submodule.subset_span (hmemS1 i hi)) ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ (deg i) (χmem i₁ : ClassFunction ↥L ℂ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
  -- `χ − χ̄` and `χ − a·χ₁` are `A₀`-supported (`Samb = univ` makes the span clause vacuous)
  · refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_univ_iff.mpr ?_
    rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj
      = -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) from by abel,
      ClassFunction.support_neg]
    exact hdiffsuppχ
  · exact OddOrder.Peterfalvi.S07.mem_zSupportedSpan_univ_iff.mpr hdiffasuppχ

open scoped Classical in
/-- **Norm-weighted (5.6) forward adjoin engine, reducible BREAK (`‖χ‖² ≠ 1`).**

The `‖χ‖² ≠ 1` analogue of `xAdjoinStepW`: the **break** pair `{χ, χ̄}` may itself be a
reducible certain-type column (`‖χ‖² = w₁ > 1`), not just the non-anchor members.  The break
decomposition `Da : CharacterPsiDecomposition τ χ (a·χ₁)` is therefore taken as a **parameter**
(constructed by `certainTypeDecompositionDa` from the (5.3.b) σ-image family `R(μ_j)`), rather than
built internally by `decompositionDaFromDadeOfDiff` (irreducible-only, via the conjugate-pair Dade
family `dadeOrthonormalCharacterImageFamilyOfDiff`).  The break image family `R(χ) = Da.imageFamily`
then feeds the (5.2.e) cross-family orthogonality `hortho_mem` and the crux-2 vanishing.

The only extra hypothesis over `xAdjoinStepW` is `hDatau1 : Da.tau1 = τ` (the break
decomposition's auxiliary isometry is the Dade base map itself — holds by `rfl` for
`certainTypeDecompositionDa`), used to read the (5.4) image equation `τ(χ − a·χ₁) = Da.X − Da.Y`
(`hYeq`) off `Da.tau1_image`.  The norm-1 hypotheses `hχχ`/`hχbarχbar` of `xAdjoinStepW` become the
non-vanishing `hχχne`/`hχbarχbarne`, and the bridge is the reducible
`retarget_isCoherent_of_extensionImage_k`. -/
noncomputable def xAdjoinStepW_k
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : ClassFunction ↥L ℂ)
    (hdiffsuppχ : (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχne : ClassFunction.inner χ χ ≠ 0)
    (hχbarχbarne : ClassFunction.inner χ.conj χ.conj ≠ 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0)
    (hχbarχ : ClassFunction.inner χ.conj χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    {a : ℕ}
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χmem i) 0)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      χ (a • χmem i₁))
    (hDatau1 : Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData))
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily)
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    (hdiffasuppχ : (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {χ - χ.conj, χ - a • (χmem i₁ : ClassFunction ↥L ℂ)})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {χ, χ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- The Dade map is an isometry on **every** supported set, so the ambient family of the general
  -- engine is `Samb = univ` and `hisom` is `dade_hisom_of_zSupportedSpan` there.
  refine OddOrder.Peterfalvi.S07.xAdjoinStepW_k_general (Samb := Set.univ) hS₁ (Set.subset_univ _)
    (dade_hisom_of_zSupportedSpan hyp Set.univ) χ hχχne hχbarχbarne hχχbar hχbarχ hχ_S1 hχbar_S1
    s χmem deg i₁ hi₁ ?_ hmemS1 mc hmempos hmemortho Dmem Da hDatau1 hortho_mem htau1Dmem
    ?_ ?_ htau1_memaχ ha1 hDeg hSgen hgen
  -- the scaled member differences lie in the `A₀`-supported part of `ℤ[S₁]`
  · intro i hi
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, hmemdegdiffsupp i hi⟩
    refine Submodule.sub_mem _ (Submodule.subset_span (hmemS1 i hi)) ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ (deg i) (χmem i₁ : ClassFunction ↥L ℂ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
  -- `χ − χ̄` and `χ − a·χ₁` are `A₀`-supported (`Samb = univ` makes the span clause vacuous)
  · refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_univ_iff.mpr ?_
    rw [show χ - χ.conj = -(χ.conj - χ) from by abel, ClassFunction.support_neg]
    exact hdiffsuppχ
  · exact OddOrder.Peterfalvi.S07.mem_zSupportedSpan_univ_iff.mpr hdiffasuppχ

open scoped Classical in
/-- **Norm-weighted (5.6) degree-square bound (contrapositive of `xAdjoinStepW`).**

The norm-weighted Peterfalvi (5.6) inequality: if `S₁` is coherent but `S₁ ∪ {χ, χ̄}` is **not**,
then
the weighted degree-square sum is bounded by twice the degree ratio,
`∑_{i∈s} deg(i)² / ‖χmem i‖² ≤ 2a`.  This is the reducible-member generalization of
`coherentDegreeSumBound_of_not_coherent` (the case-A `‖χmem i‖² = 1` specialization, with conclusion
`∑ deg² ≤ 2a`).

Pure contrapositive of the forward engine `xAdjoinStepW`: were the bound to fail
(`2a < ∑ deg²/mc`), `xAdjoinStepW` would produce coherence of `S₁ ∪ {χ, χ̄}`, contradicting `hnc`.
All the per-member decomposition data (`Dmem`/`hortho_mem`/`htau1Dmem`) is threaded through
unchanged — for case (B) it is supplied per member from `certainTypeDecompositionDa`/`certainTypeR`
(reducible certain-type columns) and `memberExtensionDecomposition` (irreducible members). -/
theorem coherentDegreeSqNormBound_of_not_coherentW
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χmem i) 0)
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hrealχ
        hdiffsuppχ))
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)}))
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i ≤ 2 * (a : ℝ) := by
  by_contra hlt
  push Not at hlt
  exact hnc ⟨xAdjoinStepW hyp hS₁ χ hrealχ hdiffsuppχ hχχ hχbarχbar hχχbar hχbarχ
    hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ hmemdegdiffsupp hmemS1 mc hmempos hmemortho
    Dmem hortho_mem htau1Dmem hdiffasuppχ htau1_memaχ ha1 hlt hSgen hgen⟩

open scoped Classical in
/-- **Norm-weighted (5.6) degree-square bound, reducible BREAK (contrapositive of
`xAdjoinStepW_k`).**

The `‖χ‖² ≠ 1` analogue of `coherentDegreeSqNormBound_of_not_coherentW`: if `S₁` is coherent but
`S₁ ∪ {χ, χ̄}` is **not** — for a possibly **reducible** break `χ` whose decomposition `Da` is
supplied as a parameter — then the weighted degree-square sum is bounded,
`∑ deg(i)²/‖χmem i‖² ≤ 2a`.
Pure contrapositive of the reducible-break forward engine `xAdjoinStepW_k`. -/
theorem coherentDegreeSqNormBound_of_not_coherentW_k
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : ClassFunction ↥L ℂ)
    (hdiffsuppχ : (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχne : ClassFunction.inner χ χ ≠ 0)
    (hχbarχbarne : ClassFunction.inner χ.conj χ.conj ≠ 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0)
    (hχbarχ : ClassFunction.inner χ.conj χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    {a : ℕ}
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χmem i) 0)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      χ (a • χmem i₁))
    (hDatau1 : Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData))
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily)
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    (hdiffasuppχ : (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {χ - χ.conj, χ - a • (χmem i₁ : ClassFunction ↥L ℂ)}))
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {χ, χ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i ≤ 2 * (a : ℝ) := by
  by_contra hlt
  push Not at hlt
  exact hnc ⟨xAdjoinStepW_k hyp hS₁ χ hdiffsuppχ hχχne hχbarχbarne hχχbar hχbarχ
    hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ hmemdegdiffsupp hmemS1 mc hmempos hmemortho
    Dmem Da hDatau1 hortho_mem htau1Dmem hdiffasuppχ htau1_memaχ ha1 hlt hSgen hgen⟩

end OddOrder.Peterfalvi.S08


