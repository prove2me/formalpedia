-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
-- name    : OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:50:03.961879+00:00
-- url     : https://prove2.me/theorems/0d61e31a-998a-4133-9215-e11b513bf5c3
-- title:
--   Peterfalvi §10: Dade calculations (continuation)
-- statement:
--   A continuation of the §10 Dade calculations, centered on the signed $\sigma$-image family of the $\mu$-columns and the orthonormal character image families built from it.
--
--   Main declarations: `Hypothesis.columnRImage_inner` (Orthonormality of `R(μ_j)`); `Hypothesis.columnRImage_injective` (`R(μ_j)` is injective on `Bool × Fin w₁` (distinct orthonormal vectors are distinct)); `Hypothesis.columnRImage_sum` (The sum of the §10 `R(μ_j)` family over `Bool × Fin w₁` is `δ·∑_i (ω_{ij}^σ − ω_{ij'}^σ)`, the…); `Hypothesis.columnImageFamily` (§10 column `OrthonormalCharacterImageFamily`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/DadeCalculations.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/DadeCalculations.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Isometry106

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Orthonormality of `R(μ_j)`** at §10: the signed σ-image family `columnRImage` is orthonormal,
`⟨R p, R q⟩ = δ_{p,q}`.  The sign `δ = ±1` gives `δ·δ̄ = 1`, the σ-grid orthonormality
`alignedOmegaSigmaGrid_inner` supplies `⟨ω_{ij}^σ, ω_{i'j'}^σ⟩ = [i=i' ∧ j=j']`, and the two halves
(`j ≠ j'`) are cross-orthogonal. -/
theorem Hypothesis.columnRImage_inner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    {j j' : Fin hyp.w2} (hjj' : j ≠ j') (p q : Bool × Fin hyp.w1) :
    ClassFunction.inner (hyp.columnRImage hG hodd δ j j' p) (hyp.columnRImage hG hodd δ j j' q)
      = if p = q then (1 : ℂ) else 0 := by
  have hδstar : star ((δ : ℂ)) = (δ : ℂ) := by rcases hδ with h | h <;> rw [h] <;> norm_num
  have hδsq : (δ : ℂ) * (δ : ℂ) = 1 := by rcases hδ with h | h <;> rw [h] <;> norm_num
  obtain ⟨bp, ip⟩ := p
  obtain ⟨bq, iq⟩ := q
  cases bp <;> cases bq <;>
    simp only [Hypothesis.columnRImage, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hyp.alignedOmegaSigmaGrid_inner hG hodd,
      hδstar, star_neg, mul_neg, neg_mul, neg_neg, Prod.mk.injEq, reduceCtorEq, false_and,
      true_and, and_true, ↓reduceIte]
  · -- (false,false): same column `j`, `δ²·[ip=iq] = [ip=iq]`
    rw [← mul_assoc, hδsq, one_mul]
  · -- (false,true): cross column `j ≠ j'`
    rw [if_neg (fun hcon => hjj' hcon.2)]; ring
  · -- (true,false): cross column `j' ≠ j`
    rw [if_neg (fun hcon => hjj' hcon.2.symm)]; ring
  · -- (true,true): same column `j'`, `δ²·[ip=iq] = [ip=iq]`
    rw [← mul_assoc, hδsq, one_mul]

open scoped FiniteInduce in
/-- `R(μ_j)` is injective on `Bool × Fin w₁` (distinct orthonormal vectors are distinct). -/
theorem Hypothesis.columnRImage_injective [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    {j j' : Fin hyp.w2} (hjj' : j ≠ j') :
    Function.Injective (hyp.columnRImage hG hodd δ j j') := by
  intro p q hpq
  by_contra hpqne
  have h0 := hyp.columnRImage_inner hG hodd hδ hjj' p q
  rw [if_neg hpqne, hpq, hyp.columnRImage_inner hG hodd hδ hjj', if_pos rfl] at h0
  exact one_ne_zero h0

open scoped FiniteInduce in
/-- The sum of the §10 `R(μ_j)` family over `Bool × Fin w₁` is `δ·∑_i (ω_{ij}^σ − ω_{ij'}^σ)`, the
image side of the (10.6)(a) summed isometry (`tau_muGrid_columnSum_diff`). -/
theorem Hypothesis.columnRImage_sum [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (δ : ℤ) (j j' : Fin hyp.w2) :
    ∑ p : Bool × Fin hyp.w1, hyp.columnRImage hG hodd δ j j' p
      = (δ : ℂ) • ∑ i : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i j') := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Finset.smul_sum]
  simp only [Hypothesis.columnRImage, neg_smul, smul_sub]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by abel)

open scoped Classical FiniteInduce in
/-- **§10 column `OrthonormalCharacterImageFamily`** (Peterfalvi (5.2.d) for the reducible column
`μ_j`): the difference-image family `R(μ_j) = {δ·ω_{ij}^σ} ∪ {−δ·ω_{ij'}^σ}` of the column character
`μ_j = ∑_i μ_{ij}` against the §10 Dade isometry `hyp.tau`.  This is the §10 analogue of the §6
`certainTypeR`, built directly on `hyp.tau` (an `IntegralCharacterMap`) instead of the §6 Dade map.

The `image_eq` field `hyp.tau(μ_j − μ̄_j) = ∑ R(μ_j)` combines the conjugate-column identity
`μ̄_j = μ_{j'}` (`hconj`, from `exists_conj_column`), the (10.5) summed isometry
`tau_muGrid_columnSum_diff` (`hyp.tau(μ_j − μ_{j'}) = δ(∑ω_{ij}^σ − ∑ω_{ij'}^σ)`), and
`columnRImage_sum`; `orthonormal`/`mem_ZIrr` come from `columnRImage_inner`/`_injective` and
`alignedOmegaSigmaGrid_mem_ZIrr`.  Feeding `ofProjection` (with `coh.tau1`, ψ = 0), the (5.5)
`eq_sum_of_psi_eq_zero` then computes `μ_j^{τ₁} = ∑_{E ⊆ R(μ_j)} α`. -/
noncomputable def Hypothesis.columnImageFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j j' : Fin hyp.w2} (hj0 : j ≠ 0) (hj'0 : j' ≠ 0) (hjj' : j ≠ j')
    (hconj : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j).conj
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j') :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau
      (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) where
  imageSet := Finset.univ.image (hyp.columnRImage hG hG.odd params.delta j j')
  mem_ZIrr := by
    intro α hα
    rw [Finset.mem_image] at hα
    obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
    cases b
    · simp only [Hypothesis.columnRImage]
      rw [Int.cast_smul_eq_zsmul]
      exact (ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j)
    · simp only [Hypothesis.columnRImage]
      rw [neg_smul, Int.cast_smul_eq_zsmul]
      exact neg_mem ((ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j'))
  orthonormal := by
    intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨p, _, rfl⟩ := hα
    obtain ⟨q, _, rfl⟩ := hβ
    rw [hyp.columnRImage_inner hG hG.odd hδpm hjj']
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [if_neg hpq,
        if_neg (fun he => hpq (hyp.columnRImage_injective hG hG.odd hδpm hjj' he))]
  image_eq := by
    rw [hconj, tau_muGrid_columnSum_diff hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hj'0,
      Finset.sum_image (fun p _ q _ hpq => hyp.columnRImage_injective hG hG.odd hδpm hjj' hpq),
      hyp.columnRImage_sum, Finset.sum_sub_distrib]

open scoped Classical FiniteInduce in
/-- **§10 column `OrthonormalCharacterImageFamily`, coherence-free** ((5.2.d) for the reducible
column
`μ_j`): the difference-image family `R(μ_j) = {δ·ω_{ij}^σ} ∪ {−δ·ω_{ij'}^σ}` of the column character
`μ_j = ∑_i μ_{ij}` against the §10 Dade isometry `hyp.tau`.  This is the §10 analogue of the §6
`certainTypeR`, built directly on `hyp.tau` (an `IntegralCharacterMap`) instead of the §6 Dade map.

The `image_eq` field `hyp.tau(μ_j − μ̄_j) = ∑ R(μ_j)` combines the conjugate-column identity
`μ̄_j = μ_{j'}` (`hconj`, from `exists_conj_column`), the (10.5) summed isometry
`tau_muGrid_columnSum_diff` (`hyp.tau(μ_j − μ_{j'}) = δ(∑ω_{ij}^σ − ∑ω_{ij'}^σ)`), and
`columnRImage_sum`; `orthonormal`/`mem_ZIrr` come from `columnRImage_inner`/`_injective` and
`alignedOmegaSigmaGrid_mem_ZIrr`.  Feeding `ofProjection` (with `coh.tau1`, ψ = 0), the (5.5)
`eq_sum_of_psi_eq_zero` then computes `μ_j^{τ₁} = ∑_{E ⊆ R(μ_j)} α`. -/
noncomputable def Hypothesis.columnImageFamilyCohFree [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (_hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j j' : Fin hyp.w2} (hj0 : j ≠ 0) (hj'0 : j' ≠ 0) (hjj' : j ≠ j')
    (hconj : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j).conj
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j') :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau
      (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) where
  imageSet := Finset.univ.image (hyp.columnRImage hG hG.odd params.delta j j')
  mem_ZIrr := by
    intro α hα
    rw [Finset.mem_image] at hα
    obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
    cases b
    · simp only [Hypothesis.columnRImage]
      rw [Int.cast_smul_eq_zsmul]
      exact (ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j)
    · simp only [Hypothesis.columnRImage]
      rw [neg_smul, Int.cast_smul_eq_zsmul]
      exact neg_mem ((ZIrr G).smul_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i j'))
  orthonormal := by
    intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨p, _, rfl⟩ := hα
    obtain ⟨q, _, rfl⟩ := hβ
    rw [hyp.columnRImage_inner hG hG.odd hδpm hjj']
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [if_neg hpq,
        if_neg (fun he => hpq (hyp.columnRImage_injective hG hG.odd hδpm hjj' he))]
  image_eq := by
    rw [hconj, hyp.tau_muGrid_columnSum_diff_cohFree hG hG.odd hmu hzS hz1 hδpm hδj hj0 hj'0 hjj',
      Finset.sum_image (fun p _ q _ hpq => hyp.columnRImage_injective hG hG.odd hδpm hjj' hpq),
      hyp.columnRImage_sum, Finset.sum_sub_distrib]

open scoped Classical FiniteInduce in
/-- **§10 (5.5) for the column `μ_j`** (Peterfalvi (5.5) applied to the reducible column character):
`μ_j^{τ₁} = ∑_{α ∈ E} α` for some `E ⊆ R(μ_j)` with `|E| = ‖μ_j‖² = w₁`.

Builds the (5.4) `CharacterPsiDecomposition` for `(μ_j, ψ = 0)` against `τ = hyp.tau`,
`τ₁ = coh.tau1` via `ofProjection` — the column `OrthonormalCharacterImageFamily`
(`columnImageFamily`) supplies `R(μ_j)`; the coherence isometry `coh.coherent` supplies the
lattice-relative inner-preservation (`extension_inner_eq`, on `ℤ[S] ⊇ {μ_j − μ̄_j, μ_j}`), the
`τ`-agreement (`extends_on_supported`, `μ_j − μ̄_j` is `A_0`-supported), and the `ZIrr`-membership
(`extension_mem_ZIrr`, `μ_j ∈ S`); the orthogonalities `⟨μ_j, 0⟩ = ⟨μ̄_j, 0⟩ = 0` are trivial and
`⟨μ_j, μ̄_j⟩ = 0` is the cross-column Gram entry (`muGrid_inner_cross_column`, `j ≠ j'`).  Then
`eq_sum_of_psi_eq_zero` extracts the (5.5) sum.  This is the second-to-last step of (10.6)(a); the
final (5.8) full-column endgame then pins `E` to the single full column `{δ·ω_{ij}^σ}`. -/
theorem Hypothesis.exists_muColumn_tau1_eq_sum_R [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hd1 : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hG.odd 0 jj 1 ≠ 1)
    {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    ∃ j' : Fin hyp.w2, j' ≠ 0 ∧ j' ≠ j ∧
      ∃ E ⊆ Finset.univ.image (hyp.columnRImage hG hG.odd params.delta j j'),
        coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) = ∑ α ∈ E, α ∧
          (E.card : ℂ) = (hyp.w1 : ℂ) := by
  have := hyp.finiteG
  classical
  obtain ⟨j', hj'0, hj'j, hconj⟩ := hyp.exists_conj_column hG hG.odd hj0
  set χ := ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j with hχdef
  have hχS : χ ∈ inducedFamily M := hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd j (hd1 j hj0)
  have hχcS : χ.conj ∈ inducedFamily M := by
    rw [hχdef, hconj]; exact hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd j' (hd1 j' hj'0)
  -- `χ − χ̄ = ∑_i (α_{ij} − α_{ij'})` is `A_0`-supported and lies in `ℤ[S]`.
  have hμdiff : χ - χ.conj
      = ∑ i : Fin hyp.w1, (params.alpha i j - params.alpha i j') := by
    rw [hχdef, hconj, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [params.alpha_def, params.alpha_def, hmu]; abel
  have hsumsupp : ∀ s : Finset (Fin hyp.w1),
      (∑ i ∈ s, (params.alpha i j - params.alpha i j')).support ⊆ hyp.A0 := by
    intro s
    induction s using Finset.induction with
    | empty => rw [Finset.sum_empty, ClassFunction.support_zero]; exact Set.empty_subset _
    | insert i s hi ih =>
        rw [Finset.sum_insert hi]
        refine (ClassFunction.support_add_subset _ _).trans (Set.union_subset ?_ ih)
        exact (ClassFunction.support_sub_subset _ _).trans
          (Set.union_subset (params.alpha_support i j hj0) (params.alpha_support i j' hj'0))
  have hsuppmem : (χ - χ.conj) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 :=
    ⟨Submodule.sub_mem _ (Submodule.subset_span hχS) (Submodule.subset_span hχcS),
      by rw [hμdiff]; exact hsumsupp Finset.univ⟩
  -- the running coherence isometry preserves inner products on `ℤ[S] ⊇ zSpan {χ − χ̄, χ − 0}`.
  have hspan : OddOrder.Peterfalvi.S07.zSpan (L := ↥M) {χ - χ.conj, χ - 0}
      ≤ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.sub_mem _ (Submodule.subset_span hχS) (Submodule.subset_span hχcS)
    · rw [sub_zero]; exact Submodule.subset_span hχS
  -- `⟨μ_j, μ̄_j⟩ = 0` (cross-column Gram entry).
  have hχχbar : ClassFunction.inner χ χ.conj = 0 := by
    rw [hχdef, hconj, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_eq_zero fun i' _ => hyp.muGrid_inner_cross_column hG hG.odd i i' hj'j.symm
  -- assemble the (5.4) decomposition via `ofProjection` and apply (5.5).
  let R := hyp.columnImageFamily hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 hj'0
    (Ne.symm hj'j) hconj
  let D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau χ 0 :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection R coh.tau1
      (fun φ ζ hφ hζ => coh.coherent.extension_inner_eq φ ζ (hspan hφ) (hspan hζ))
      (coh.coherent.extends_on_supported _ hsuppmem)
      (by rw [sub_zero]; exact coh.coherent.extension_mem_ZIrr χ (Submodule.subset_span hχS))
      (by rw [ClassFunction.inner_zero_right])
      (by rw [ClassFunction.inner_zero_right])
      hχχbar
  obtain ⟨_, hτ1, E, hEsub, hEsum, hEcard⟩ := D.eq_sum_of_psi_eq_zero
  refine ⟨j', hj'0, hj'j, E, hEsub, ?_, ?_⟩
  · rw [← hEsum]; exact hτ1
  · rw [hEcard, hχdef, hyp.muGrid_column_sum_inner_self hG hG.odd j]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.6)(a) summed isometry**: for every nontrivial column `0 < j < w₂`,
`μ_j^{τ₁} = δ·∑_i ω_{ij}^σ`.

This is the §10 specialisation of Peterfalvi's (5.8) — proved here *without* the general (5.8)
machinery (separability / `σ`-coefficients), using only the (10.6)(a) reduction and a cardinality
count.  By (5.5) (`exists_muColumn_tau1_eq_sum_R`), `μ_j^{τ₁} = ∑_{x ∈ T} R(x)` where
`R = R(μ_j) = {δ·ω_{ij}^σ}∪{−δ·ω_{ij'}^σ}` (`columnRImage`, `j'` the conjugate column) is an
orthonormal family and `|T| = ‖μ_j^{τ₁}‖² = w₁`.  The reduction
`(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = δ` (`omegaSigmaDiff_inner_muColumn_tau1`) computes, against the
`T`-sum, to `δ·[(false, i) ∈ T]` (the cross-column `j'` and the trivial column `0` are orthogonal);
since `δ ≠ 0`, every `(false, i) ∈ T`. So `{false} × univ ⊆ T` with both of cardinality `w₁`,
forcing
`T = {false} × univ` and `μ_j^{τ₁} = ∑_i δ·ω_{ij}^σ = δ·∑_i ω_{ij}^σ`. -/
theorem Hypothesis.muColumn_tau1_pin [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hd1 : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hG.odd 0 jj 1 ≠ 1)
    {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      = (params.delta : ℂ) • ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j := by
  have := hyp.finiteG
  classical
  -- (5.5): `μ_j^{τ₁} = ∑_{α ∈ E} α` for `E ⊆ R(μ_j)`, `|E| = w₁`.
  obtain ⟨j', hj'0, hj'j, E, hEsub, hEsum, hEcard⟩ :=
    hyp.exists_muColumn_tau1_eq_sum_R hG coh hmu hos hzS hz1 hzconj hδpm hδj hd1 hj0
  set R := hyp.columnRImage hG hG.odd params.delta j j' with hRdef
  have hRinj : Function.Injective R := hyp.columnRImage_injective hG hG.odd hδpm (Ne.symm hj'j)
  -- the preimage `T ⊆ Bool × Fin w₁` of `E` under the injective family `R`.
  set T : Finset (Bool × Fin hyp.w1) := Finset.univ.filter (fun x => R x ∈ E) with hTdef
  have hImT : T.image R = E := by
    apply Finset.ext; intro α
    simp only [Finset.mem_image, hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hα
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp (hEsub hα)
      exact ⟨x, by rw [hx]; exact hα, hx⟩
  have hSumT : ∑ x ∈ T, R x = ∑ α ∈ E, α := by
    rw [← hImT, Finset.sum_image (fun x _ y _ h => hRinj h)]
  have hCardT : T.card = hyp.w1 := by
    have hc : (T.image R).card = E.card := by rw [hImT]
    rw [Finset.card_image_of_injOn (fun x _ y _ h => hRinj h)] at hc
    rw [hc]; exact_mod_cast hEcard
  -- `μ_j^{τ₁} = ∑_{x ∈ T} R x`.
  have hμT : coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) = ∑ x ∈ T, R x := by
    rw [hEsum, hSumT]
  -- inner product of `ω_{ij}^σ − ω_{i0}^σ` against each `R(x)` (only `x = (false, i)` survives).
  have hval : ∀ (i : Fin hyp.w1) (x : Bool × Fin hyp.w1),
      ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - hyp.alignedOmegaSigmaGrid hG hG.odd i 0) (R x)
      = if x = (false, i) then (params.delta : ℂ) else 0 := by
    intro i x
    have hδstar : star ((params.delta : ℂ)) = (params.delta : ℂ) := by
      rcases hδpm with h | h <;> rw [h] <;> norm_num
    obtain ⟨b, i'⟩ := x
    cases b <;>
      simp only [hRdef, Hypothesis.columnRImage, ClassFunction.inner_sub_left,
        OddOrder.RepresentationTheory.inner_smul_right, hyp.alignedOmegaSigmaGrid_inner hG hG.odd,
        hδstar, star_neg, Prod.mk.injEq, reduceCtorEq, false_and, true_and, and_true,
        ↓reduceIte, neg_mul]
    · -- (false, i'): `δ · [i = i'] − δ · [i = i' ∧ 0 = j] = if i' = i then δ else 0`
      rw [if_neg (show ¬(i = i' ∧ (0 : Fin hyp.w2) = j) from fun hh => hj0 hh.2.symm),
        mul_zero, sub_zero]
      by_cases hii : i = i'
      · rw [if_pos hii, mul_one, if_pos hii.symm]
      · rw [if_neg hii, mul_zero, if_neg (fun h => hii h.symm)]
    · -- (true, i'): both columns orthogonal (`j ≠ j'`, `j' ≠ 0`)
      rw [if_neg (show ¬(i = i' ∧ j = j') from fun hh => hj'j hh.2.symm),
        if_neg (show ¬(i = i' ∧ (0 : Fin hyp.w2) = j') from fun hh => hj'0 hh.2.symm)]
      ring
  -- the (10.6)(a) reduction forces every `(false, i) ∈ T`.
  have hfalseT : ∀ i : Fin hyp.w1, (false, i) ∈ T := by
    intro i
    by_contra hni
    have hRi := hyp.omegaSigmaDiff_inner_muColumn_tau1 hG coh hmu hos hzS hz1 hzconj hδpm hδj hj0 i
    rw [hμT, OddOrder.RepresentationTheory.inner_sum_right] at hRi
    rw [show (∑ x ∈ T, ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
          - hyp.alignedOmegaSigmaGrid hG hG.odd i 0) (R x))
        = if (false, i) ∈ T then (params.delta : ℂ) else 0 by
      rw [Finset.sum_congr rfl (fun x _ => hval i x)]; exact Finset.sum_ite_eq' T (false, i) _,
      if_neg hni] at hRi
    rcases hδpm with h | h <;> rw [h] at hRi <;> norm_num at hRi
  -- `{false} × univ ⊆ T` and `|T| = w₁ = |{false} × univ|`, so `T = {false} × univ`.
  have hFsub : Finset.univ.image (fun i : Fin hyp.w1 => (false, i)) ⊆ T := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hfalseT i
  have hFinj : Function.Injective (fun i : Fin hyp.w1 => (false, i)) :=
    fun a b h => congrArg Prod.snd h
  have hFcard : (Finset.univ.image (fun i : Fin hyp.w1 => (false, i))).card = hyp.w1 := by
    rw [Finset.card_image_of_injective _ hFinj, Finset.card_univ, Fintype.card_fin]
  have hTeq : T = Finset.univ.image (fun i : Fin hyp.w1 => (false, i)) :=
    (Finset.eq_of_subset_of_card_le hFsub (by rw [hFcard, hCardT])).symm
  -- conclude: `μ_j^{τ₁} = ∑_i δ·ω_{ij}^σ = δ·∑_i ω_{ij}^σ`.
  rw [hμT, hTeq, Finset.sum_image (fun a _ b _ h => hFinj h)]
  simp only [hRdef, Hypothesis.columnRImage]
  rw [Finset.smul_sum]

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a), second identity** — the book's "Also,
`(μ_0 − ζ)^τ = ∑_{0≤i<w₁} ω_{i0}^σ − ζ^{τ₁}`" (p. 59), which is also the `Ã(M)`-independent
half of the (10.6)(b) argument.  Holds under Hypothesis (10.4) alone (no `w₁ < w₂`, no §11
input); the coherence-free (10.9) restatement, where the residual is *not* identified with
`ζ^{τ₁}`, is `exists_residual_of_w1_lt_w2`.

Picks a fixed nontrivial column `k`; the `M`-level identity
`δ(μ_0 − ζ) = (μ_k − dζ) − ∑_i α_{ik}` (from `α_{ik} = μ_{ik} − δμ_{i0} − nζ` and `d = w₁n + δ`)
is mapped through the `ℤ`-linear Dade map `τ`.  Then `τ(μ_k − dζ) = δ∑_i ω_{ik}^σ − dζ^{τ₁}`
(`μ_k − dζ = (μ_k − dζ̄) + d(ζ̄ − ζ)` reduces it to `tau_muColumn_sub_conj_eq_tau1` +
`tau_zeta_sub_conj_eq_tau1`, then `muColumn_tau1_pin` for `μ_k^{τ₁}`) and
`τ(α_{ik}) = δ(ω_{ik}^σ − ω_{i0}^σ) − nζ^{τ₁}` (`alpha_tau_image`); the `δ∑ω_{ik}^σ` cancel and
`(w₁n − d)ζ^{τ₁} = −δζ^{τ₁}`, giving `δ·τ(μ_0 − ζ) = δ∑ω_{i0}^σ − δζ^{τ₁}`; cancel `δ` (`δ² = 1`).

This is `STEP 1` of (10.6)(b) (issue 1009); the remaining `STEP 2` (`τ(μ_0 − ζ)` vanishes off
`Ã(M)`,
the tame support) + `STEP 3` parity then give `|ζ^{τ₁}(g)| ≥ 1`. -/
theorem Hypothesis.tau_muColumnZero_sub_zeta_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - params.zeta)
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) - coh.tau1 params.zeta := by
  have := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  -- a fixed nontrivial column `k`.
  have hw2 : 3 ≤ hyp.w2 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W2
  obtain ⟨k, hk0⟩ : ∃ k : Fin hyp.w2, k ≠ 0 :=
    ⟨⟨1, by omega⟩, Fin.ne_of_val_ne (by simp)⟩
  have hcolk : ∀ i, hyp.muGrid hG hodd i k 1 = (params.d : ℂ) := fun i => by
    rw [← hmu]; exact params.degree_independent i k hk0
  have hd1 : params.d ≠ 1 := by have := params.d_gt_one; omega
  have hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1 := by rw [hcolk 0]; exact_mod_cast hd1
  have hd1k : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hodd 0 jj 1 ≠ 1 := fun jj hjj => by
    rw [← hmu, params.degree_independent 0 jj hjj]; exact_mod_cast hd1
  -- `d = w₁·n + δ`.
  have hd : (params.d : ℂ) = (hyp.w1 : ℂ) * (params.n : ℂ) + (params.delta : ℂ) := by
    have h : (params.n : ℂ) * (hyp.w1 : ℂ) = (params.d : ℂ) - (params.delta : ℂ) := by
      exact_mod_cast params.n_formula
    linear_combination -h
  -- `τ` commutes with the natural scalar `d`.
  have hsmul_tau : ∀ (x : ClassFunction ↥M ℂ),
      hyp.tau ((params.d : ℂ) • x) = (params.d : ℂ) • hyp.tau x := fun x => by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul (R := ℂ)]
  -- `τ(μ_k − dζ) = δ∑ω_{ik}^σ − dζ^{τ₁}` via the conjugate decomposition.
  have htauμk : hyp.tau ((∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta)
      = (params.delta : ℂ) • (∑ i, hyp.alignedOmegaSigmaGrid hG hodd i k)
        - (params.d : ℂ) • coh.tau1 params.zeta := by
    have hdecomp : (∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta
        = ((∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta.conj)
          + (params.d : ℂ) • (params.zeta.conj - params.zeta) := by
      rw [smul_sub]; abel
    have htauzc : hyp.tau (params.zeta.conj - params.zeta)
        = coh.tau1 params.zeta.conj - coh.tau1 params.zeta := by
      rw [show params.zeta.conj - params.zeta = -(params.zeta - params.zeta.conj) by abel, map_neg,
        hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hzS params.zeta_irreducible]
      abel
    rw [hdecomp, map_add,
      hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd k coh hzS params.zeta_irreducible hcolk hz1 hdk1,
      hsmul_tau, htauzc,
      muColumn_tau1_pin hG coh hmu hos hzS hz1 hzconj hδpm hδj hd1k hk0]
    module
  -- `τ(α_{ik}) = δ(ω_{ik}^σ − ω_{i0}^σ) − nζ^{τ₁}` (the (10.5) Dade image).
  have htauα : ∀ i, hyp.tau (params.alpha i k)
      = (params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i k
          - hyp.alignedOmegaSigmaGrid hG hodd i 0) - (params.n : ℂ) • coh.tau1 params.zeta := by
    intro i
    have h := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i k hk0
    rwa [hos] at h
  -- the `M`-level identity `δ(μ_0 − ζ) = (μ_k − dζ) − ∑_i α_{ik}`.
  have hMlevel : (params.delta : ℂ) • ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)
      = ((∑ i, hyp.muGrid hG hodd i k) - (params.d : ℂ) • params.zeta) - ∑ i, params.alpha i k := by
    have hαe : (∑ i, params.alpha i k)
        = (∑ i, hyp.muGrid hG hodd i k) - (params.delta : ℂ) • (∑ i, hyp.muGrid hG hodd i 0)
          - ((hyp.w1 : ℂ) * (params.n : ℂ)) • params.zeta := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [params.alpha_def, hmu]),
        Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul]
    rw [hαe, hd]; module
  -- `∑_i (δ(ω_{ik}^σ − ω_{i0}^σ) − nζ^{τ₁}) = δ(∑ω_{ik}^σ − ∑ω_{i0}^σ) − (w₁n)ζ^{τ₁}`.
  have hsum_α : (∑ i, ((params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i k
        - hyp.alignedOmegaSigmaGrid hG hodd i 0) - (params.n : ℂ) • coh.tau1 params.zeta))
      = (params.delta : ℂ) • ((∑ i, hyp.alignedOmegaSigmaGrid hG hodd i k)
          - ∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - ((hyp.w1 : ℂ) * (params.n : ℂ)) • coh.tau1 params.zeta := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [← Finset.smul_sum, Finset.sum_sub_distrib]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ),
        smul_smul]
  -- map the `M`-level identity through `τ` and substitute the three images.
  have hscaled : (params.delta : ℂ) • hyp.tau ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)
      = (params.delta : ℂ) • ((∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0)
          - coh.tau1 params.zeta) := by
    have hkey := congrArg hyp.tau hMlevel
    rw [Int.cast_smul_eq_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul (R := ℂ)] at hkey
    rw [hkey, map_sub, htauμk, map_sum, Finset.sum_congr rfl (fun i _ => htauα i), hsum_α, hd]
    module
  -- cancel `δ` (`δ² = 1`).
  have hδsq : (params.delta : ℂ) * (params.delta : ℂ) = 1 := by
    rcases hδpm with h | h <;> rw [h] <;> norm_num
  calc hyp.tau ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)
      = (params.delta : ℂ) • ((params.delta : ℂ)
          • hyp.tau ((∑ i, hyp.muGrid hG hodd i 0) - params.zeta)) := by
        rw [smul_smul, hδsq, one_smul]
    _ = (params.delta : ℂ) • ((params.delta : ℂ) • ((∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0)
          - coh.tau1 params.zeta)) := by rw [hscaled]
    _ = (∑ i, hyp.alignedOmegaSigmaGrid hG hodd i 0) - coh.tau1 params.zeta := by
        rw [smul_smul, hδsq, one_smul]

open scoped FiniteInduce in
/-- **§10 (2.7) adjoint at the trivial character**: for an `A_0`-supported class function `φ` on
`M`,
the Dade image `φ^τ = hyp.tau φ` has the same trivial-character multiplicity as `φ`,
`⟨φ^τ, 1_G⟩ = ⟨φ, 1_M⟩`.

The genuine §10 Dade isometry `hyp.tau` agrees on the supported subspace with the §4 Dade map
`hyp.dadeData.dade.dadeMap` (`dadeIntegralCharacterMap_apply_of_support`); the Peterfalvi (2.7)
adjoint
formula `adjoint_formula` with `χ = 1_G` gives `⟨dadeMap ⟨φ,_⟩, 1_G⟩ = ⟨φ, ψ⟩`, where the coset
average `ψ = adjointAverageFun 1_G` is the constant `1` (`|H(a)|⁻¹·∑_{x ∈ H(a)} 1 = 1`), i.e. the
trivial character `1_M`.  This is the `a_{00} = ((μ_0 − ζ)^τ, 1_G) = (μ_0 − ζ, 1_M)` computation
underlying Peterfalvi (10.9). -/
theorem Hypothesis.tau_inner_trivial [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0) :
    ClassFunction.inner (hyp.tau φ) (trivialClassFunction G)
      = ClassFunction.inner φ (trivialClassFunction (↥M)) := by
  have := hyp.finiteG
  classical
  have hmem : φ ∈ ClassFunction.supportedSubmodule (G := ↥M) (k := ℂ)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M) :=
    (ClassFunction.mem_supportedSubmodule).mpr hφ
  -- `hyp.tau φ = dadeMap ⟨φ, supported⟩` on the supported subspace.
  have he : hyp.tau φ = hyp.dadeData.dade.dadeMap (k := ℂ) ⟨φ, hmem⟩ := by
    change OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData) φ
      = hyp.dadeData.dade.dadeMap (k := ℂ) ⟨φ, hmem⟩
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade _ hφ]
  -- the coset average of `1_G` is the constant `1` (= `1_M`).
  have hψ : ∀ a : {a : G // a ∈ typePA0 M hyp.typeP},
      (trivialClassFunction (↥M)) ⟨a.1, hyp.dadeData.dade.subset_L a.2⟩
        = OddOrder.Peterfalvi.S04.adjointAverageFun hyp.dadeData.dade (trivialClassFunction G)
            ⟨a.1, hyp.dadeData.dade.subset_L a.2⟩ := by
    intro a
    rw [OddOrder.Peterfalvi.S04.adjointAverageFun, dif_pos a.2]
    simp only [trivialClassFunction_apply, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_univ, ← Nat.card_eq_fintype_card]
    rw [inv_mul_cancel₀]
    exact_mod_cast Nat.card_pos.ne'
  rw [he]
  exact OddOrder.Peterfalvi.S04.adjoint_formula hyp.dadeData.dade hyp.dadeData.dade.dadeMap
    (hyp.dadeData.dade.isDadeMap_dadeMap (k := ℂ)) ⟨φ, hmem⟩ (trivialClassFunction G)
    (trivialClassFunction (↥M)) hψ

open scoped FiniteInduce in
/-- **§10 Dade isometry vanishes off the tame support `Ã(M) = dadeSupport`.**  For a class function
`φ` on `M` supported on `A_0(M)`, the Dade image `φ^τ = hyp.tau φ` *vanishes* at any
`g ∉ Ã(M) = hyp.dadeData.dade.dadeSupport`.

The genuine §10 Dade isometry `hyp.tau` is `S07.dadeIntegralCharacterMap hyp.dadeData.dade …`; on
the
supported subspace it agrees with the §4 Dade map `hyp.dadeData.dade.dadeMap`
(`dadeIntegralCharacterMap_apply_of_support`), which vanishes off `dadeSupport`
(`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport`). This is the general "vanishes off `Ã(M)`"
companion
of `dadeIntegralCharacterMap_apply_one_eq_zero` (the `g = 1` special case), and the `Ã(M)`-vanishing
step of (10.6)(b) (issue 1009, STEP 2). -/
theorem Hypothesis.tau_apply_eq_zero_of_not_mem_dadeSupport [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0)
    {g : G} (hg : g ∉ hyp.dadeData.dade.dadeSupport) :
    hyp.tau φ g = 0 := by
  have := hyp.finiteG
  classical
  change OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData) φ g = 0
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade _ hφ]
  exact (hyp.dadeData.dade.isDadeMap_dadeMap (k := ℂ)).map_eq_zero_of_not_mem_dadeSupport
    (⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ :
      OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ (typePA0 M hyp.typeP) M) g hg

open scoped FiniteInduce in
/-- **§10 support of `μ_0 − ζ`** (Peterfalvi (10.6)(b), the `Ã(M)`-vanishing leg): the column-`0`
sum `μ_0 = ∑_i μ_{i0}` (an induced character of degree `w₁`, since each `μ_{i0}(1) = 1`) minus a
degree-`w₁` irreducible `ζ ∈ S` (induced from `M'`) is supported in `A_0(M)`.

Both `μ_0` and `ζ` are induced from the normal `M' = [M,M]`, hence vanish off `M'`
(`muGrid_column_sum_vanishes_off_derived`; induced-from-`M'` for `ζ`); and the degrees cancel,
`(μ_0 − ζ)(1) = w₁ − w₁ = 0` (`muGrid_zero_column_apply_one`), so the support lies in
`M'^# ⊆ A(M) ⊆ A_0(M)`.

This is the companion of `muColumn_sub_conj_support`/`zeta_sub_conj_support`: it makes `μ_0 − ζ`
`A_0`-supported, so the Dade isometry `τ` vanishes on it off `Ã(M)`
(`tau_apply_eq_zero_of_not_mem_dadeSupport`).  Together with the (10.6)(a) identity
`τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}` (`tau_muColumnZero_sub_zeta_eq`) it yields the pointwise
identity `ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)` off `Ã(M)`. -/
theorem Hypothesis.muColumnZero_sub_zeta_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ).support ⊆ hyp.A0 := by
  have := hyp.finiteG
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hsumapply : ∀ (w : ↥M), (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) w
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 w := by
    intro w
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.muGrid hG hodd i 0) w = ∑ i ∈ s, hyp.muGrid hG hodd i 0 w) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else `μ_0 z = ζ z = 0`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, hyp.muGrid_column_sum_vanishes_off_derived hG hodd 0 hzK,
      hζvanish hzK, sub_zero]
  -- `z ≠ 1`: `(μ_0 − ζ)(1) = w₁ − w₁ = 0`.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, hζ1, hsumapply 1,
      Finset.sum_congr rfl (fun i _ => hyp.muGrid_zero_column_apply_one hG hodd i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_self]
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  change (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 2** (the `Ã(M)`-vanishing reduction): off the tame support
`Ã(M) = dadeSupport`, the coherent image `ζ^{τ₁}` agrees with the column-`0` σ-sum,
`ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)` for `g ∉ hyp.dadeData.dade.dadeSupport`.

Combines the (10.6)(a) identity `τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}`
(`tau_muColumnZero_sub_zeta_eq`, STEP 1) with the vanishing of `τ(μ_0 − ζ)` off `Ã(M)`
(`tau_apply_eq_zero_of_not_mem_dadeSupport`, since `μ_0 − ζ` is `A_0`-supported by
`muColumnZero_sub_zeta_support`).  This is STEP 2 of (10.6)(b) (issue 1009); the remaining STEP 3
(parity of `∑_i ω_{i0}^σ(g)` using `ω_{00}^σ = 1_G` and the conjugate-pairing of the `i > 0`
terms) then gives `|ζ^{τ₁}(g)| ≥ 1`. -/
theorem Hypothesis.zeta_tau1_apply_eq_omegaSigma_sum_of_not_mem_dadeSupport [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {g : G} (hg : g ∉ hyp.dadeData.dade.dadeSupport) :
    coh.tau1 params.zeta g
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g := by
  have := hyp.finiteG
  -- STEP 1: `τ(μ_0 − ζ) = ∑_i ω_{i0}^σ − ζ^{τ₁}` as class functions on `G`.
  have hstep1 := hyp.tau_muColumnZero_sub_zeta_eq hG coh hmu hos hzS hz1 hzconj hδpm hδj
  -- `μ_0 − ζ` is `A_0`-supported, so `τ(μ_0 − ζ)` vanishes off `Ã(M)`.
  have hsupp := hyp.muColumnZero_sub_zeta_support hG hG.odd hzS hz1
  have hvanish := hyp.tau_apply_eq_zero_of_not_mem_dadeSupport hsupp hg
  -- Evaluate the STEP 1 identity at `g` (`ClassFunction` is a `CoeFun`, not `DFunLike`).
  have heval : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - params.zeta) g
      = ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
          - coh.tau1 params.zeta) g :=
    congrArg (fun f : ClassFunction G ℂ => (f : G → ℂ) g) hstep1
  -- Cancel the vanishing left-hand side.
  rw [ClassFunction.sub_apply, hvanish] at heval
  linear_combination heval

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (10.6)(b), STEP 3 — integrality of the column-`0` σ-grid value** ((3.9)(c) on the
aligned grid): for `g : G` of order prime to `w₁`, each `ω_{i0}^σ(g)` is a rational integer.

The aligned grid is `ω_{i0}^σ = σ(ω(ξ_i))` for the transported linear character
`ξ_i = (omegaProdChar (w1CharEquiv i) χ₂).comp e` of `tic.W` (column-`0` dual `χ₂ = 1`).  As column
`0` is trivial, `ξ_i` factors through `W₁` (`omegaProdChar_one_right`), so
`orderOf ξ_i ∣ |W₁| = w₁`;
since `(orderOf g)` is coprime to `w₁` it is coprime to `orderOf ξ_i`, and (3.9)(c)
(`exists_intCast_sigma_omega_apply`) gives the integer. -/
theorem Hypothesis.exists_intCast_alignedOmegaSigmaGrid_zero_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {g : G}
    (hg : (orderOf g).Coprime hyp.w1) :
    ∃ n : ℤ, hyp.alignedOmegaSigmaGrid hG hodd i 0 g = (n : ℂ) := by
  have := hyp.finiteG
  classical
  -- reconstruct the `let`s of `alignedOmegaSigmaGrid`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the transported linear character `ξ` of `tic.W`
  let ξ : ↥tic.W →* ℂˣ :=
    (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm i)) χ₂).comp
      e.toMonoidHom
  -- `alignedOmegaSigmaGrid i 0 = σ(ω ξ)` (mirror the `step1` of the χ-family lemma; `ω = lin`).
  have step1 : hyp.alignedOmegaSigmaGrid hG hodd i 0
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega ξ : ClassFunction ↥tic.W ℂ) := by
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega ξ : ClassFunction ↥tic.W ℂ)
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega ξ : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- column `0` dual is trivial, so `ξ = (w1CharEquiv …).comp wFst ∘ e` factors through `W₁`.
  have hχ₂ : χ₂ = 1 := by
    change finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1
    rw [show (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 0 from by simp,
      finCardEquivCharacterGroup_zero]
  -- `(w1CharEquiv …) ^ w₁ = 1` from `|Ŵ₁| = |W₁| = w₁` (Pontryagin self-duality).
  have hcardDual : Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = hyp.w1 :=
    (h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf
      h.sdiffTICyclicHypothesis.W1_le_W).trans hcardW1
  have hχ1pow : (h.w1CharEquiv (finCongr hcardW1.symm i)) ^ hyp.w1 = 1 := by
    have := pow_card_eq_one' (x := h.w1CharEquiv (finCongr hcardW1.symm i))
    rwa [hcardDual] at this
  -- column `0` trivial ⟹ `ξ` factors through `W₁` as `(w1CharEquiv …).comp wFst ∘ e`.
  have hξeq : ξ = ((h.w1CharEquiv (finCongr hcardW1.symm i)).comp
      h.sdiffTICyclicHypothesis.wFst).comp e.toMonoidHom := by
    have hpc : (h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm i)) χ₂)
        = (h.w1CharEquiv (finCongr hcardW1.symm i)).comp h.sdiffTICyclicHypothesis.wFst := by
      rw [hχ₂]
      exact h.sdiffTICyclicHypothesis.omegaProdChar_one_right _
    exact congrArg (fun f => f.comp e.toMonoidHom) hpc
  -- `ξ ^ w₁ = 1` pointwise.
  have hξpow : ξ ^ hyp.w1 = 1 := by
    refine MonoidHom.ext fun w => Units.val_injective ?_
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one, hξeq,
      MonoidHom.comp_apply, MonoidHom.comp_apply, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply,
      hχ1pow, MonoidHom.one_apply, Units.val_one]
  have hdvd : orderOf ξ ∣ hyp.w1 := orderOf_dvd_of_pow_eq_one hξpow
  have hcop : (orderOf g).Coprime (orderOf ξ) := hg.coprime_dvd_right hdvd
  obtain ⟨n, hn⟩ :=
    tic.exists_intCast_sigma_omega_apply rfl (hyp.canonicalFullDadeApp hG hodd) ξ hcop
  exact ⟨n, by rw [step1]; exact hn⟩

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (10.6)(b), STEP 3 — the principal grid value** ((4.4)/(3.2)(b)): the `(0,0)` entry
of the aligned σ-grid is the trivial character `1_G`, `ω_{00}^σ = 1_G`.

For `i = 0`, column `0`: the source `ξ_{00} = (omegaProdChar (w1CharEquiv 0) χ₂).comp e` is trivial
—
`w1CharEquiv 0 = 1` (`w1CharEquiv_zero`), `χ₂ = 1` (column `0`), so `omegaProdChar 1 1 = 1`
(`omegaProdChar_one_one`) and `(1).comp e = 1`.  Then `tic.omega 1 = 1_{tic.W}` and
`1_{tic.W}^σ = 1_G` (`sigma_trivial`). -/
theorem Hypothesis.alignedOmegaSigmaGrid_zero_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    hyp.alignedOmegaSigmaGrid hG hodd 0 0 = trivialClassFunction G := by
  have := hyp.finiteG
  classical
  -- reconstruct the `let`s of `alignedOmegaSigmaGrid`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  let ξ : ↥tic.W →* ℂˣ :=
    (h.sdiffTICyclicHypothesis.omegaProdChar
      (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)))
      χ₂).comp e.toMonoidHom
  -- `alignedOmegaSigmaGrid 0 0 = σ(ω ξ)` (mirror the `step1` of the χ-family lemma).
  have step1 : hyp.alignedOmegaSigmaGrid hG hodd 0 0
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega ξ : ClassFunction ↥tic.W ℂ) := by
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega ξ : ClassFunction ↥tic.W ℂ)
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega ξ : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- both indices trivial ⟹ `ξ = 1`.
  have hχ₂ : χ₂ = 1 := by
    change finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1
    rw [show (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 0 from by simp,
      finCardEquivCharacterGroup_zero]
  have hχ1 : h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 1 := by
    rw [show (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 0 from by simp, h.w1CharEquiv_zero]
  have hξ1 : ξ = 1 := by
    have hpc : h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) χ₂ = 1 := by
      rw [hχ₂, hχ1]; exact h.sdiffTICyclicHypothesis.omegaProdChar_one_one
    change (h.sdiffTICyclicHypothesis.omegaProdChar
      (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) χ₂).comp e.toMonoidHom = 1
    rw [hpc, MonoidHom.one_comp]
  -- `tic.omega 1 = 1_{tic.W}`, and `1_{tic.W}^σ = 1_G`.
  have homega1 : (tic.omega (1 : ↥tic.W →* ℂˣ) : ClassFunction ↥tic.W ℂ)
      = trivialClassFunction ↥tic.W := by ext w; simp
  rw [step1, hξ1, homega1, OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_trivial]

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (10.6)(b), STEP 3 — the row-conjugation involution** ((3.9)(a)/(4.9)(a) on the
aligned column-`0` grid): complex conjugation of `ω_{i0}^σ` is again a column-`0` grid value
`ω_{i'0}^σ`, where `i' = rowInv i` is the **row-inversion** index (`w1CharEquiv i' =
(w1CharEquiv i)⁻¹`); moreover `i' = i ↔ i = 0` (in the odd-order dual `Ŵ₁`, `χ⁻¹ = χ ⟺ χ = 1`), and
`i ↦ i'` is an involution.

`mapRingEquiv conj (ω_{i0}^σ) = sigma(galoisMap conj (ω(ξ_i))) = sigma(ω(ξ_i⁻¹))`
(`sigma_mapRingEquiv_comm` + `galoisMap_conj_omega`), and `ξ_i⁻¹ = ξ_{i'}` since
`omegaProdChar χ₁ χ₂` inverts coordinatewise (`omegaProdChar_inv`), `w1CharEquiv (rowInv i) =
(w1CharEquiv i)⁻¹` (`w1CharEquiv_rowInv`) and `χ₂⁻¹ = χ₂` (column `0` is trivial).  This is the
(3.9)(a) ingredient that pairs the `i > 0` terms of `∑_i ω_{i0}^σ(g)`. -/
theorem Hypothesis.exists_rowInv_alignedOmegaSigma_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) :
    ∃ i' : Fin hyp.w1,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
          (hyp.alignedOmegaSigmaGrid hG hodd i 0)
        = hyp.alignedOmegaSigmaGrid hG hodd i' 0
      ∧ (i' = i ↔ i = 0)
      ∧ (∀ j' : Fin hyp.w1,
          (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
              (hyp.alignedOmegaSigmaGrid hG hodd i' 0)
            = hyp.alignedOmegaSigmaGrid hG hodd j' 0) → j' = i) := by
  have := hyp.finiteG
  classical
  -- reconstruct the `let`s of `alignedOmegaSigmaGrid`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the transported linear character `ξ_a` of `tic.W` for any row `a`
  let ξ : Fin hyp.w1 → (↥tic.W →* ℂˣ) := fun a =>
    (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm a)) χ₂).comp
      e.toMonoidHom
  -- `alignedOmegaSigmaGrid a 0 = σ(ω ξ_a)` for any row `a`.
  have step1 : ∀ a, hyp.alignedOmegaSigmaGrid hG hodd a 0
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega (ξ a) : ClassFunction ↥tic.W ℂ) := by
    intro a
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega (ξ a) : ClassFunction ↥tic.W ℂ)
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (tic.omega (ξ a) : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- column `0` dual is trivial: `χ₂ = 1` (so `χ₂⁻¹ = χ₂`).
  have hχ₂ : χ₂ = 1 := by
    change finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1
    rw [show (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 0 from by simp,
      finCardEquivCharacterGroup_zero]
  -- the row-inversion translated index
  let i' : Fin hyp.w1 :=
    finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i))
  -- `finCongr` round-trip: `finCongr hcardW1.symm i' = rowInv (finCongr hcardW1.symm i)`.
  have hround : finCongr hcardW1.symm i'
      = OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i) := by
    change finCongr hcardW1.symm
        (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i)))
      = OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i)
    simp
  -- `χ₂⁻¹ = χ₂` (column `0` is trivial).
  have hχ₂inv : χ₂⁻¹ = χ₂ := by
    rw [hχ₂]
    exact @inv_one ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _
  -- key: `mapRingEquiv conj (ω_{a0}^σ) = ω_{a'0}^σ` for a row `a` with translated index `a'`.
  have hconj : ∀ a : Fin hyp.w1,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.alignedOmegaSigmaGrid hG hodd a 0)
        = hyp.alignedOmegaSigmaGrid hG hodd
            (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a))) 0 := by
    intro a
    have hroundA : finCongr hcardW1.symm
        (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a)))
      = OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a) := by simp
    -- `ξ_a⁻¹ = ξ_{a'}`.
    have hξinv : (ξ a)⁻¹
        = ξ (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a))) := by
      -- the underlying `omegaProdChar` factors invert; `χ₂⁻¹ = χ₂`, row inverts via `rowInv`.
      have hprod : (h.sdiffTICyclicHypothesis.omegaProdChar
            (h.w1CharEquiv (finCongr hcardW1.symm a)) χ₂)⁻¹
          = h.sdiffTICyclicHypothesis.omegaProdChar
              (h.w1CharEquiv (finCongr hcardW1.symm
                (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a)))))
                χ₂ := by
        rw [hroundA, OddOrder.Peterfalvi.S06.w1CharEquiv_rowInv,
          OddOrder.Peterfalvi.S06.omegaProdChar_inv, hχ₂]
        congr 1
      change ((h.sdiffTICyclicHypothesis.omegaProdChar
          (h.w1CharEquiv (finCongr hcardW1.symm a)) χ₂).comp e.toMonoidHom)⁻¹
        = (h.sdiffTICyclicHypothesis.omegaProdChar
          (h.w1CharEquiv (finCongr hcardW1.symm
            (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a)))))
              χ₂).comp e.toMonoidHom
      refine MonoidHom.ext fun w => Units.val_injective ?_
      rw [MonoidHom.comp_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, ← hprod,
        MonoidHom.inv_apply]
    rw [step1 a,
      step1 (finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm a))),
      tic.sigma_mapRingEquiv_comm rfl (hyp.canonicalFullDadeApp hG hodd) _ _,
      OddOrder.Peterfalvi.S06.galoisMap_conj_omega, hξinv]
  -- oddness of the dual `Ŵ₁` (from `Odd |G|` via `W₁ ≤ M ≤ G` and Pontryagin).
  have hcardDual : Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = hyp.w1 :=
    (h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf
      h.sdiffTICyclicHypothesis.W1_le_W).trans hcardW1
  have hoddM : Odd (Nat.card ↥M) := Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card M)
  have hoddW1 : Odd (Nat.card ↥h.W1) :=
    Odd.of_dvd_nat hoddM (Subgroup.card_subgroup_dvd_card h.W1)
  -- in the odd-order dual, `χ⁻¹ = χ ⟹ χ = 1`.
  have hsq_one : ∀ χ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ, χ⁻¹ = χ → χ = 1 := by
    intro χ hχ
    have : Finite ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Finite.of_fintype _
    have hx2 : χ ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← hχ]; exact inv_mul_cancel χ
    have h2 : orderOf χ ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hc : orderOf χ ∣ Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := orderOf_dvd_natCard χ
    have hcop : Nat.Coprime 2 (Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) := by
      rw [Nat.coprime_two_left, hcardDual, ← hcardW1]; exact hoddW1
    have hg : orderOf χ ∣ Nat.gcd 2 (Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) :=
      Nat.dvd_gcd h2 hc
    rw [hcop.gcd_eq_one] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  refine ⟨i', hconj i, ?_, ?_⟩
  · -- `i' = i ↔ i = 0`.
    constructor
    · intro hii
      have hceq : (h.w1CharEquiv (finCongr hcardW1.symm i))⁻¹
          = h.w1CharEquiv (finCongr hcardW1.symm i) := by
        rw [← OddOrder.Peterfalvi.S06.w1CharEquiv_rowInv, ← hround, hii]
      have hx1 : h.w1CharEquiv (finCongr hcardW1.symm i) = 1 := hsq_one _ hceq
      have hz : finCongr hcardW1.symm i = 0 :=
        h.w1CharEquiv.injective (hx1.trans h.w1CharEquiv_zero.symm)
      have h0 : i = finCongr hcardW1 (0 : Fin (Nat.card h.W1)) := by rw [← hz]; simp
      rw [h0]; simp
    · intro hi0
      have hz : finCongr hcardW1.symm i = 0 := by rw [hi0]; simp
      change finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i)) = i
      rw [hz]
      have hrow0 : OddOrder.Peterfalvi.S06.rowInv h (0 : Fin (Nat.card h.W1)) = 0 := by
        have h_inv_one :
            ((1 : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)⁻¹) = 1 :=
          @inv_one ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _
        rw [OddOrder.Peterfalvi.S06.rowInv, h.w1CharEquiv_zero, h_inv_one]
        exact h.w1CharEquiv.symm_apply_eq.mpr h.w1CharEquiv_zero.symm
      rw [hrow0, hi0]; simp
  · -- involution: applying the construction to `i'` returns `i`.
    intro j' hj'
    have hkey := hconj i'
    rw [hj'] at hkey
    have hii : finCongr hcardW1 (OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm i'))
        = i := by
      rw [hround, OddOrder.Peterfalvi.S06.rowInv_rowInv]; simp
    rw [hii] at hkey
    -- `hkey : ω_{j'0}^σ = ω_{i0}^σ`.  Conclude `j' = i` via grid orthonormality.
    by_contra hne
    have hortho := hyp.alignedOmegaSigmaGrid_inner hG hodd j' i 0 0
    rw [hkey, hyp.alignedOmegaSigmaGrid_inner hG hodd i i 0 0, if_pos ⟨rfl, rfl⟩,
      if_neg (fun hc => hne hc.1)] at hortho
    exact one_ne_zero hortho

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(b), STEP 3 — the parity bound** (the (10.6)(b) target): off the tame support
`Ã(M)`, at a `g` of order prime to `w₁`, the coherent image `ζ^{τ₁}(g)` is an **odd integer**.

By STEP 2 (`zeta_tau1_apply_eq_omegaSigma_sum_of_not_mem_dadeSupport`),
`ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)`.  Each `ω_{i0}^σ(g)` is a rational integer `n_i`
(`exists_intCast_alignedOmegaSigmaGrid_zero_column`, (3.9)(c)), so `ζ^{τ₁}(g) = (∑_i n_i : ℤ)`.
The terms pair under the row-conjugation involution `i ↦ i'`
(`exists_rowInv_alignedOmegaSigma_conj`,
(3.9)(a)): `n_{i'} = n_i` (conjugation fixes the real integer), and the unique fixed point `i = 0`
carries the principal value `n_0 = 1` (`alignedOmegaSigmaGrid_zero_zero`, `ω_{00}^σ = 1_G`). Hence
the
off-principal terms sum to an even integer and `∑_i n_i = 1 + even` is odd; in particular
`|ζ^{τ₁}(g)| ≥ 1`.  This closes (10.6)(b) (issue 1009). -/
theorem Hypothesis.zeta_tau1_norm_ge_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {g : G} (hg : g ∉ hyp.dadeData.dade.dadeSupport) (hgord : (orderOf g).Coprime hyp.w1) :
    ∃ m : ℤ, coh.tau1 params.zeta g = (m : ℂ) ∧ Odd m := by
  have := hyp.finiteG
  classical
  -- STEP 2: `ζ^{τ₁}(g) = ∑_i ω_{i0}^σ(g)`.
  have hstep2 := hyp.zeta_tau1_apply_eq_omegaSigma_sum_of_not_mem_dadeSupport
    hG coh hmu hos hzS hz1 hzconj hδpm hδj hg
  -- push the application through the finite sum (CoeFun, not DFunLike).
  have hsumapply : (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g
      = ∑ i : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g := by
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g
        = ∑ i ∈ s, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  -- (3.9)(c): each `ω_{i0}^σ(g)` is a rational integer `n i`.
  have hint : ∀ i : Fin hyp.w1,
      ∃ n : ℤ, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g = (n : ℂ) := fun i =>
    hyp.exists_intCast_alignedOmegaSigmaGrid_zero_column hG hG.odd i hgord
  let n : Fin hyp.w1 → ℤ := fun i => (hint i).choose
  have hn : ∀ i, (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) g = (n i : ℂ) :=
    fun i => (hint i).choose_spec
  -- `m := ∑ n i`, and `ζ^{τ₁}(g) = (m : ℂ)`.
  have hval : coh.tau1 params.zeta g = ((∑ i : Fin hyp.w1, n i : ℤ) : ℂ) := by
    rw [hstep2, hsumapply]
    push_cast
    exact Finset.sum_congr rfl (fun i _ => hn i)
  refine ⟨∑ i : Fin hyp.w1, n i, hval, ?_⟩
  -- the row-conjugation involution `ρ` ((3.9)(a)).
  have hB : ∀ a : Fin hyp.w1, ∃ i' : Fin hyp.w1,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
        (hyp.alignedOmegaSigmaGrid hG hG.odd a 0)
        = hyp.alignedOmegaSigmaGrid hG hG.odd i' 0
      ∧ (i' = a ↔ a = 0)
      ∧ (∀ j' : Fin hyp.w1,
          (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
              (hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
            = hyp.alignedOmegaSigmaGrid hG hG.odd j' 0) → j' = a) := fun a =>
    hyp.exists_rowInv_alignedOmegaSigma_conj hG hG.odd a
  let ρ : Fin hyp.w1 → Fin hyp.w1 := fun a => (hB a).choose
  have hρconj : ∀ a, ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
        (hyp.alignedOmegaSigmaGrid hG hG.odd a 0)
      = hyp.alignedOmegaSigmaGrid hG hG.odd (ρ a) 0 := fun a => (hB a).choose_spec.1
  have hρfix : ∀ a, ρ a = a ↔ a = 0 := fun a => (hB a).choose_spec.2.1
  have hρinv : ∀ a, ρ (ρ a) = a := fun a => (hB a).choose_spec.2.2 (ρ (ρ a)) (hρconj (ρ a))
  -- the involution preserves `n`: `n (ρ a) = n a` (conjugation fixes the real integer).
  have hnρ : ∀ a, n (ρ a) = n a := by
    intro a
    have hc := congrArg (fun f : ClassFunction G ℂ => (f : G → ℂ) g) (hρconj a)
    simp only [ClassFunction.mapRingEquiv_apply] at hc
    rw [hn a, hn (ρ a), map_intCast] at hc
    exact_mod_cast hc.symm
  -- `n 0 = 1` (the principal value `ω_{00}^σ = 1_G`).
  have hn0 : n 0 = 1 := by
    have h00 := hyp.alignedOmegaSigmaGrid_zero_zero hG hG.odd
    have := hn 0
    rw [h00, trivialClassFunction_apply] at this
    exact_mod_cast this.symm
  -- off-principal terms sum to an even integer (fixed-point-free involution on `univ ∖ {0}`).
  have heven : (2 : ℤ) ∣ ∑ i ∈ Finset.univ.erase (0 : Fin hyp.w1), n i := by
    have hz : ((∑ i ∈ Finset.univ.erase (0 : Fin hyp.w1), n i : ℤ) : ZMod 2) = 0 := by
      push_cast
      refine Finset.sum_involution (fun a _ => ρ a) ?_ ?_ ?_ ?_
      · intro a _
        rw [hnρ a]; exact CharTwo.add_self_eq_zero _
      · intro a ha _ hcontra
        exact (Finset.mem_erase.mp ha).1 ((hρfix a).mp hcontra)
      · intro a ha
        rw [Finset.mem_erase] at ha ⊢
        refine ⟨fun hcontra => ha.1 ?_, Finset.mem_univ _⟩
        have hca : ρ a = 0 := hcontra
        calc a = ρ (ρ a) := (hρinv a).symm
          _ = ρ 0 := by rw [hca]
          _ = 0 := (hρfix 0).mpr rfl
      · intro a _; exact hρinv a
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz
  -- `∑ n i = n 0 + (even) = 1 + even` is odd.
  have hsplit : (∑ i : Fin hyp.w1, n i)
      = n 0 + ∑ i ∈ Finset.univ.erase (0 : Fin hyp.w1), n i :=
    (Finset.add_sum_erase Finset.univ n (Finset.mem_univ 0)).symm
  rw [hsplit, hn0]
  rcases heven with ⟨c, hc⟩
  exact ⟨c, by rw [hc]; ring⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)**: the sums of `omega_ij^sigma` describe the `tau1`
images, and outside the tame support the value of `zeta^tau1` has norm at least
one.

Conjunct (a) (the summed isometry) is the genuine `muColumn_tau1_pin` (the §10 specialisation of
(5.8)). Conjunct (b) (the (10.6)(b) parity bound) is now genuine and proven: off
`Ã(M) = dadeSupport`,
at `g` of order prime to `w₁`, `ζ^{τ₁}(g)` is an **odd integer** (`zeta_tau1_norm_ge_one`), hence
`|ζ^{τ₁}(g)| ≥ 1` — replacing the former opaque `zeta_tau1_norm_bound` placeholder field.  The
(10.3)/(10.5) carrier pins (`hmu`/`hos`/`hzS`/`hz1`/`hzconj`/`hδpm`/`hδj`) are discharged by the
constructed `params` (`w2_prime_and_parameter_independence`). -/
theorem tau1_values_and_norm_bound [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    (∀ (j : Fin hyp.w2), j ≠ 0 →
        coh.tau1 (∑ i : Fin hyp.w1, params.mu i j) =
          (params.delta : ℂ) • ∑ i : Fin hyp.w1, params.omegaSigma i j) ∧
      (∀ (g : G), g ∉ hyp.dadeData.dade.dadeSupport → (orderOf g).Coprime hyp.w1 →
          ∃ m : ℤ, coh.tau1 params.zeta g = (m : ℂ) ∧ Odd m) := by
  have hd1 : ∀ jj : Fin hyp.w2, jj ≠ 0 → hyp.muGrid hG hG.odd 0 jj 1 ≠ 1 := by
    intro jj hjj
    rw [← hmu, params.degree_independent 0 jj hjj]
    exact_mod_cast (by have := params.d_gt_one; omega : params.d ≠ 1)
  refine ⟨fun j hj0 => ?_, ?_⟩
  · -- (10.6)(a): the summed isometry `μ_j^{τ₁} = δ·∑_i ω_{ij}^σ`.
    rw [hmu, hos]
    exact hyp.muColumn_tau1_pin hG coh hmu hos hzS hz1 hzconj hδpm hδj hd1 hj0
  · -- (10.6)(b): off `Ã(M)`, at `g` of order prime to `w₁`, `ζ^{τ₁}(g)` is an odd integer
    -- (`zeta_tau1_norm_ge_one`); in particular `|ζ^{τ₁}(g)| ≥ 1`.
    intro g hg hgord
    exact hyp.zeta_tau1_norm_ge_one hG coh hmu hos hzS hz1 hzconj hδpm hδj hg hgord

end OddOrder.Peterfalvi.S12


