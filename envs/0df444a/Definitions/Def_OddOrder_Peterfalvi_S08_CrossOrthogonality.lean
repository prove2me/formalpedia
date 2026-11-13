-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CrossOrthogonality
-- name    : OddOrder_Peterfalvi_S08_CrossOrthogonality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:13:38.090018+00:00
-- url     : https://prove2.me/theorems/ea39220d-1c76-4a1b-8047-b82743431a22
-- title:
--   Peterfalvi (5.2.e)/(5.3.b): reducible-column vs irreducible-break cross-orthogonality
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §5. This file states the mixed stratum of the (5.2.e) cross-family orthogonality at Hypothesis (4.6) generality, between the reducible certain-type column image family and an irreducible break family.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CrossOrthogonality.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CrossOrthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBCoherence2

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

section

/-- **Peterfalvi (5.2.e), mixed stratum** `R(μ_j) ⊥ R(χ)` at Hypothesis (4.6) generality.

Let `h46` be a Hypothesis (4.6) datum (supplying the certain-type column family and its
`ticVdiff` exceptional structure) and let `dade` be any Hypothesis (2.2) Dade datum on `A`
with `τ` its integral character map.  If the conjugate difference `(χ − χ̄)^τ` of an
irreducible non-real `χ` vanishes on the exceptional set `V` — the **anchor** `htauvanish` —
then every member of the reducible column image family `R(μ_j)` is orthogonal to every
member of the irreducible break family `R(χ)`.

The anchor is the only place where the ambient FT situation enters; the three call sites
(Sibley §8, type-P §13, type-II §12) each discharge it by their own route. -/
theorem certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV
    {A₀ : Set G} (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A₀ L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    {A : Set G} (dade : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htauvanish : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap dade (dade.fullDadeIsometryData)
        ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) v = 0) :
    ∀ α ∈ (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).imageSet,
    ∀ β ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff dade χ
        hrealχ hdiffsuppχ).imageSet,
      ClassFunction.inner α β = 0 := by
  classical
  -- `hmin`: `2 < min(w₁, w₂)` for the `ticVdiff` exceptional structure.
  have hmin : 2 < min (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W1)
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W2) := by
    have h1 := (OddOrder.Peterfalvi.S06.ticVdiff h46).three_le_card_W1
    have h2 := (OddOrder.Peterfalvi.S06.ticVdiff h46).three_le_card_W2
    omega
  -- **Core disjointness brick.**  For any column `χ₂'`, row `i`, and a normalized orthonormal pair
  -- `ξ, ξ'` whose signed difference `c·ξ − c'·ξ'` vanishes on `V`, the σ-image `ω_{ij}^σ` is
  -- orthogonal to `c·ξ`.
  have key : ∀ (χ₂' : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ)
      (i : Fin (Nat.card h46.W1)) {c c' : ℂ} {ξ ξ' : ClassFunction G ℂ},
      ξ ∈ ZIrr G → ClassFunction.inner ξ ξ = 1 → ξ' ∈ ZIrr G → ClassFunction.inner ξ' ξ' = 1 →
      ClassFunction.inner ξ ξ' = 0 → c ≠ 0 →
      (∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, (c • ξ - c' • ξ') v = 0) →
      ClassFunction.inner (c • ξ)
        (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂' i) = 0 := by
    intro χ₂' i c c' ξ ξ' hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish
    rw [OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_eq_chiFam]
    exact inner_smul_chiFam_eq_zero_of_diff_vanishOnV (OddOrder.Peterfalvi.S06.ticVdiff h46) rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication h46) hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish
      hmin _
  -- Capture the underlying two-element `CharacterDifferenceImage` `R(χ) = {ε·μ, −ε·ν}` abstractly
  -- (its `(1.4)` proof obligations are inferred by `rfl`), so we never reconstruct them by hand.
  obtain ⟨cd, hcd⟩ :
      ∃ cd : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap dade
          (dade.fullDadeIsometryData)) (χ : ClassFunction ↥L ℂ),
        OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff dade χ
            hrealχ hdiffsuppχ
          = cd.toOrthonormalImage := ⟨_, rfl⟩
  -- `R(χ).image_eq` rewritten in `ε·μ − ε·ν` form, equal to `(χ − χ̄)^τ`, hence vanishing on `V`.
  have hcdimg : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap dade
      (dade.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)
      = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction := by
    rw [cd.image_eq, smul_sub, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  -- The `ZIrr`/orthonormality facts for `μ, ν`.
  have hμZ : cd.muClassFunction ∈ ZIrr G := cd.mu.mem_ZIrr
  have hνZ : cd.nuClassFunction ∈ ZIrr G := cd.nu.mem_ZIrr
  have hμ1 : ClassFunction.inner cd.muClassFunction cd.muClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.mu; rwa [if_pos rfl] at h
  have hν1 : ClassFunction.inner cd.nuClassFunction cd.nuClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.nu; rwa [if_pos rfl] at h
  have hμν : ClassFunction.inner cd.muClassFunction cd.nuClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.nu; rwa [if_neg cd.distinct] at h
  have hνμ : ClassFunction.inner cd.nuClassFunction cd.muClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.mu
    rwa [if_neg (Ne.symm cd.distinct)] at h
  have hsignC : (cd.sign : ℂ) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  have hnsignC : (-(cd.sign : ℂ)) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  -- Destructure α and β.
  intro α hα β hβ
  rw [hcd] at hβ
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage,
    Finset.mem_insert, Finset.mem_singleton] at hβ
  simp only [OddOrder.Peterfalvi.S06.certainTypeR, Finset.mem_image] at hα
  obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
  -- The two `(χ − χ̄)^τ`-vanishing facts for the two signed pairs `(μ, ν)` / `(ν, μ)`.
  have hvanishμν : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V,
      ((cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction) v = 0 := by
    intro v hv; rw [← hcdimg]; exact htauvanish v hv
  have hvanishνμ : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V,
      ((-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction) v = 0 := by
    intro v hv
    rw [show (-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction
        = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction by
      rw [neg_smul, neg_smul]; abel]
    exact hvanishμν v hv
  -- Normalize the `ℤ`-smul break-pair members `ε·μ`, `−ε·ν` to `ℂ`-smul (matching `key`).
  have hμcast : cd.sign • cd.muClassFunction = (cd.sign : ℂ) • cd.muClassFunction :=
    (Int.cast_smul_eq_zsmul ℂ cd.sign cd.muClassFunction).symm
  have hνcast : (-cd.sign) • cd.nuClassFunction = (-(cd.sign : ℂ)) • cd.nuClassFunction := by
    rw [← Int.cast_smul_eq_zsmul ℂ (-cd.sign) cd.nuClassFunction, Int.cast_neg]
  -- For each `β = ε·μ` or `−ε·ν`, and each `α = (±δ_j)·ω^σ`, reduce via conjugate symmetry and
  -- `key`.
  rcases hβ with rfl | rfl <;> cases b <;>
    simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
  -- Case β = ε·μ, α = δ_j·ω_{χ₂,i}^σ.
  · rw [hμcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂ i hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν, mul_zero, star_zero]
  -- Case β = ε·μ, α = −δ_j·ω_{χ₂⁻¹,i}^σ.
  · rw [hμcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂⁻¹ i hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν, mul_zero, star_zero]
  -- Case β = −ε·ν, α = δ_j·ω_{χ₂,i}^σ.
  · rw [hνcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂ i hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ, mul_zero, star_zero]
  -- Case β = −ε·ν, α = −δ_j·ω_{χ₂⁻¹,i}^σ.
  · rw [hνcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂⁻¹ i hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ, mul_zero, star_zero]

end

end OddOrder.Peterfalvi.S08


