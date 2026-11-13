-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_CoherenceGalois
-- name    : OddOrder_Peterfalvi_S07_CoherenceGalois
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:06:54.854594+00:00
-- url     : https://prove2.me/theorems/db4aee4e-4d30-4db5-a85b-e105355a0e3e
-- title:
--   Peterfalvi (5.9)(a): Galois automorphisms commute with coherent isometries
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §5, (5.9)(a): assume Hypothesis (2.2) (the §4 Dade situation). Let $\mathcal{S}\subseteq\mathrm{Irr}\,L$ with $\mathbb{Z}[\mathcal{S},L^\#]=\mathbb{Z}[\mathcal{S},A]$ and $|\mathcal{S}|\ge 2$, let $u$ be a field automorphism with $\mathcal{S}^u\subseteq\mathcal{S}$, and let $\tau_1$ be a linear isometry; then Galois automorphisms commute with the coherent isometry.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_CoherenceGalois.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_CoherenceGalois.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclotomicGaloisAction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_DifferenceImage
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_NormInequalities
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_FamilyBundleDade

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S04

variable {G : Type*} [Group G] {A : Set G} {L : Subgroup G} [Fintype G] [Fintype ↥L]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- **The explicit Dade map commutes with coefficientwise ring automorphisms** on the
supported subspace: its value at `g ∈ dadeSupport` is the evaluation `α(a)` at an `A`-base
point, and `0` elsewhere, so applying `σc` to coefficients commutes with it. -/
theorem dadeIntegralCharacterMap_mapRingEquiv_comm
    (hyp : S04.Hypothesis G A L) (dade : S04.FullDadeIsometryData (G := G) hyp)
    (σc : ℂ ≃+* ℂ) {φ : ClassFunction (↥L) ℂ}
    (hφ : φ.support ⊆ supportInSubgroup A L) :
    dadeIntegralCharacterMap hyp dade (ClassFunction.mapRingEquiv σc φ) =
      ClassFunction.mapRingEquiv σc (dadeIntegralCharacterMap hyp dade φ) := by
  have hφ' : (ClassFunction.mapRingEquiv σc φ).support ⊆ supportInSubgroup A L := by
    rwa [ClassFunction.support_mapRingEquiv]
  rw [dadeIntegralCharacterMap_apply_of_support hyp dade hφ',
    dadeIntegralCharacterMap_apply_of_support hyp dade hφ]
  ext g
  simp only [ClassFunction.mapRingEquiv_apply, Hypothesis.dadeMap_apply]
  by_cases hg : g ∈ hyp.dadeSupport
  · obtain ⟨a, h, hh, hga⟩ := hyp.mem_dadeSupport_iff.mp hg
    rw [hyp.dadeValue_eq _ hh hga, hyp.dadeValue_eq _ hh hga]
    rfl
  · rw [hyp.dadeValue_of_not_mem_dadeSupport _ hg, hyp.dadeValue_of_not_mem_dadeSupport _ hg,
      map_zero]

/-- **The Dade map restores values on `A`**: `(τ φ)(a) = φ(a)` for `a ∈ A`.

`a = a·1` with `1 ∈ H(a)`, so `a` is its own base point in the Dade-support
decomposition.  This is the evaluation step of (6.8.2.1): if `ζ ∈ ℤ[S, A]` vanishes at
`x ∈ Z^# ⊆ A`, then so does `(τ ζ)(x) = ζ(x) = 0`. -/
theorem dadeIntegralCharacterMap_apply_mem
    (hyp : S04.Hypothesis G A L) (dade : S04.FullDadeIsometryData (G := G) hyp)
    {φ : ClassFunction (↥L) ℂ} (hφ : φ.support ⊆ supportInSubgroup A L)
    {a : G} (ha : a ∈ A) :
    dadeIntegralCharacterMap hyp dade φ a = φ ⟨a, hyp.mem_L ha⟩ := by
  rw [dadeIntegralCharacterMap_apply_of_support hyp dade hφ]
  simp only [Hypothesis.dadeMap_apply]
  refine hyp.dadeValue_eq (a := ⟨a, ha⟩) _ (Subgroup.one_mem _) ?_
  rw [mul_one]

/-- **Dade images vanish at the identity**: `1 ∉ dadeSupport`. -/
theorem dadeIntegralCharacterMap_apply_one
    (hyp : S04.Hypothesis G A L) (dade : S04.FullDadeIsometryData (G := G) hyp)
    {φ : ClassFunction (↥L) ℂ} (hφ : φ.support ⊆ supportInSubgroup A L) :
    dadeIntegralCharacterMap hyp dade φ 1 = 0 := by
  rw [dadeIntegralCharacterMap_apply_of_support hyp dade hφ]
  simp only [Hypothesis.dadeMap_apply]
  exact hyp.dadeValue_of_not_mem_dadeSupport _ hyp.one_notMem_dadeSupport

/-- **Peterfalvi (5.9)(a).**  In the Dade situation, let `S ⊆ Irr L` with `|S| ≥ 2`, closed
under the coefficientwise automorphism `σc`, such that members of `ℤ[S]` vanishing at `1`
are supported on `A'` (the condition `ℤ[S, L^#] = ℤ[S, A]`).  If `τ₁ = hτ.extension` is a
coherent isometric extension of the Dade map `τ` mapping `S` into `ℤ[Irr G]`, then `τ₁`
commutes with `σc` on `S`:

`(τ₁ χ)^{σc} = τ₁ (χ^{σc})` for all `χ ∈ S`.

Proof: `ψ(1)·χ − χ(1)·ψ` vanishes at `1`, hence is supported and `τ₁ = τ` there; `τ`
commutes with `σc` by its pointwise definition, giving
`ψ(1)·(τ₁χ)^{σc} − χ(1)·(τ₁ψ)^{σc} = ψ(1)·τ₁(χ^{σc}) − χ(1)·τ₁(ψ^{σc})`.  Each `τ₁φ`
(`φ ∈ S`) is `ε·ξ_φ` with `ξ_φ ∈ Irr G` and a sign `ε` *independent of `φ`* (norm `1`
forces `±`; vanishing of Dade images at `1` forces a uniform sign).  Comparing coefficients
of the irreducible `(ξ_χ)^{σc}` in the displayed equation forces
`(ξ_χ)^{σc} = ξ_{χ^{σc}}`. -/
theorem IsCoherent.extension_mapRingEquiv_comm
    {hyp : S04.Hypothesis G A L} {dade : S04.FullDadeIsometryData (G := G) hyp}
    {S : Set (ClassFunction (↥L) ℂ)} {A' : Set ↥L}
    (hτ : IsCoherent (dadeIntegralCharacterMap hyp dade) S A')
    (hA' : A' ⊆ supportInSubgroup A L)
    (hSirr : S ⊆ irreducibleCharacters ↥L)
    (hspan : ∀ φ ∈ zSpan (L := ↥L) S, φ 1 = 0 → φ.support ⊆ A')
    (σc : ℂ ≃+* ℂ) (hSu : ∀ φ ∈ S, ClassFunction.mapRingEquiv σc φ ∈ S)
    (hlat : ∀ φ ∈ S, hτ.extension φ ∈ ZIrr G)
    {χ : ClassFunction (↥L) ℂ} (hχ : χ ∈ S)
    (h2 : ∃ ψ ∈ S, ψ ≠ χ) :
    ClassFunction.mapRingEquiv σc (hτ.extension χ) =
      hτ.extension (ClassFunction.mapRingEquiv σc χ) := by
  classical
  obtain ⟨ψ, hψ, hψχ⟩ := h2
  set τ₁ := hτ.extension with hτ₁def
  -- (i) `τ₁` commutes with `σc` on the vanishing-at-1 part of `ℤ[S]`
  have hcomm : ∀ ζ, ζ ∈ zSpan (L := ↥L) S → ζ 1 = 0 →
      ClassFunction.mapRingEquiv σc (τ₁ ζ) = τ₁ (ClassFunction.mapRingEquiv σc ζ) := by
    intro ζ hζ hζ1
    have hζsupp : ζ.support ⊆ A' := hspan ζ hζ hζ1
    have hζu : ClassFunction.mapRingEquiv σc ζ ∈ zSupportedSpan (L := ↥L) S A' := by
      refine ⟨?_, ?_⟩
      · exact Submodule.span_mono (Set.image_subset_iff.mpr hSu)
          (ClassFunction.mapRingEquiv_mem_zSpan_image σc hζ)
      · rw [ClassFunction.support_mapRingEquiv]
        exact hζsupp
    calc ClassFunction.mapRingEquiv σc (τ₁ ζ)
        = ClassFunction.mapRingEquiv σc (dadeIntegralCharacterMap hyp dade ζ) := by
          rw [hτ.extends_on_supported ζ ⟨hζ, hζsupp⟩]
      _ = dadeIntegralCharacterMap hyp dade (ClassFunction.mapRingEquiv σc ζ) :=
          (dadeIntegralCharacterMap_mapRingEquiv_comm hyp dade σc
            (hζsupp.trans hA')).symm
      _ = τ₁ (ClassFunction.mapRingEquiv σc ζ) := (hτ.extends_on_supported _ hζu).symm
  -- (ii) degrees of the members of `S`
  have hdeg : ∀ φ, φ ∈ S → ∃ d : ℕ, 0 < d ∧ φ 1 = (d : ℂ) := by
    intro φ hφ
    obtain ⟨e, he, h1⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨φ, hSirr hφ⟩ : IrreducibleCharacter ↥L)
    exact ⟨e, he, h1⟩
  choose d hdpos hd1 using hdeg
  -- (iii) `τ₁ φ = ε_φ • ξ_φ` with `ε_φ = ±1`, `ξ_φ ∈ Irr G`
  have hpm : ∀ φ (hφ : φ ∈ S), ∃ (e : ℤ) (ξ : IrreducibleCharacter G),
      (e = 1 ∨ e = -1) ∧ τ₁ φ = e • (ξ : ClassFunction G ℂ) := by
    intro φ hφ
    have hnorm : ClassFunction.inner (τ₁ φ) (τ₁ φ) = 1 := by
      rw [hτ.extension_inner_eq φ φ (Submodule.subset_span hφ) (Submodule.subset_span hφ)]
      have h := irreducibleCharacter_inner_eq_ite
        (⟨φ, hSirr hφ⟩ : IrreducibleCharacter ↥L) (⟨φ, hSirr hφ⟩ : IrreducibleCharacter ↥L)
      rw [if_pos rfl] at h
      exact h
    exact exists_zsmul_irreducibleCharacter_of_inner_self_one (hlat φ hφ) hnorm
  choose ε ξ hεpm hξrepr using hpm
  -- (iv) the signs agree pairwise (vanishing at 1 of Dade images)
  have hsign : ∀ φ₁ (h₁ : φ₁ ∈ S) φ₂ (h₂ : φ₂ ∈ S), ε φ₁ h₁ = ε φ₂ h₂ := by
    intro φ₁ h₁ φ₂ h₂
    set ζ : ClassFunction (↥L) ℂ := (d φ₂ h₂ : ℤ) • φ₁ - (d φ₁ h₁ : ℤ) • φ₂ with hζdef
    have hζspan : ζ ∈ zSpan (L := ↥L) S :=
      sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span h₁))
        (Submodule.smul_mem _ _ (Submodule.subset_span h₂))
    have hζ1 : ζ 1 = 0 := by
      rw [hζdef]
      simp only [ClassFunction.sub_apply, ClassFunction.zsmul_apply,
        hd1 φ₁ h₁, hd1 φ₂ h₂, zsmul_eq_mul]
      push_cast
      ring
    have hτζ1 : τ₁ ζ 1 = 0 := by
      rw [hτ.extends_on_supported ζ ⟨hζspan, hspan ζ hζspan hζ1⟩]
      exact dadeIntegralCharacterMap_apply_one hyp dade ((hspan ζ hζspan hζ1).trans hA')
    have hτζ : τ₁ ζ = (d φ₂ h₂ : ℤ) • τ₁ φ₁ - (d φ₁ h₁ : ℤ) • τ₁ φ₂ := by
      rw [hζdef, map_sub, map_smul, map_smul]
    obtain ⟨e₁, he₁, hξ₁⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (ξ φ₁ h₁)
    obtain ⟨e₂, he₂, hξ₂⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (ξ φ₂ h₂)
    have hkey : (d φ₂ h₂ : ℂ) * ((ε φ₁ h₁ : ℂ) * (e₁ : ℂ)) =
        (d φ₁ h₁ : ℂ) * ((ε φ₂ h₂ : ℂ) * (e₂ : ℂ)) := by
      have h0 := hτζ1
      rw [hτζ, hξrepr φ₁ h₁, hξrepr φ₂ h₂] at h0
      simp only [ClassFunction.sub_apply, ClassFunction.zsmul_apply, hξ₁, hξ₂,
        zsmul_eq_mul] at h0
      push_cast at h0
      linear_combination h0
    rcases hεpm φ₁ h₁ with hε₁ | hε₁ <;> rcases hεpm φ₂ h₂ with hε₂ | hε₂
    case inl.inl => rw [hε₁, hε₂]
    case inl.inr =>
      exfalso
      rw [hε₁, hε₂] at hkey
      push_cast at hkey
      have hsum : ((d φ₂ h₂ * e₁ + d φ₁ h₁ * e₂ : ℕ) : ℂ) = 0 := by
        push_cast
        linear_combination hkey
      have h0 : d φ₂ h₂ * e₁ + d φ₁ h₁ * e₂ = 0 := Nat.cast_eq_zero.mp hsum
      have hp1 : 0 < d φ₂ h₂ * e₁ := Nat.mul_pos (hdpos φ₂ h₂) he₁
      omega
    case inr.inl =>
      exfalso
      rw [hε₁, hε₂] at hkey
      push_cast at hkey
      have hsum : ((d φ₂ h₂ * e₁ + d φ₁ h₁ * e₂ : ℕ) : ℂ) = 0 := by
        push_cast
        linear_combination -hkey
      have h0 : d φ₂ h₂ * e₁ + d φ₁ h₁ * e₂ = 0 := Nat.cast_eq_zero.mp hsum
      have hp1 : 0 < d φ₂ h₂ * e₁ := Nat.mul_pos (hdpos φ₂ h₂) he₁
      omega
    case inr.inr => rw [hε₁, hε₂]
  -- abbreviations: the four irreducible constituents
  have hχu : ClassFunction.mapRingEquiv σc χ ∈ S := hSu χ hχ
  have hψu : ClassFunction.mapRingEquiv σc ψ ∈ S := hSu ψ hψ
  -- decomposed forms of the four images, all with the sign `ε χ hχ`
  have huτχ : ClassFunction.mapRingEquiv σc (τ₁ χ) =
      ε χ hχ • (IrreducibleCharacter.galoisMap σc (ξ χ hχ) : ClassFunction G ℂ) := by
    rw [hξrepr χ hχ, ClassFunction.mapRingEquiv_zsmul]
    rfl
  have huτψ : ClassFunction.mapRingEquiv σc (τ₁ ψ) =
      ε χ hχ • (IrreducibleCharacter.galoisMap σc (ξ ψ hψ) : ClassFunction G ℂ) := by
    rw [hξrepr ψ hψ, ClassFunction.mapRingEquiv_zsmul, hsign ψ hψ χ hχ]
    rfl
  have hτuχ : τ₁ (ClassFunction.mapRingEquiv σc χ) =
      ε χ hχ • (ξ _ hχu : ClassFunction G ℂ) := by
    rw [hξrepr _ hχu, hsign _ hχu χ hχ]
  have hτuψ : τ₁ (ClassFunction.mapRingEquiv σc ψ) =
      ε χ hχ • (ξ _ hψu : ClassFunction G ℂ) := by
    rw [hξrepr _ hψu, hsign _ hψu χ hχ]
  -- (v) the main equation, with the sign `ε χ hχ` cancelled
  have hE2 : ε χ hχ * ε χ hχ = 1 := by
    rcases hεpm χ hχ with h1 | h1 <;> rw [h1] <;> norm_num
  have hmain : (d ψ hψ : ℤ) • (IrreducibleCharacter.galoisMap σc (ξ χ hχ) : ClassFunction G ℂ)
        - (d χ hχ : ℤ) • (IrreducibleCharacter.galoisMap σc (ξ ψ hψ) : ClassFunction G ℂ)
      = (d ψ hψ : ℤ) • (ξ _ hχu : ClassFunction G ℂ)
        - (d χ hχ : ℤ) • (ξ _ hψu : ClassFunction G ℂ) := by
    set ζ₀ : ClassFunction (↥L) ℂ := (d ψ hψ : ℤ) • χ - (d χ hχ : ℤ) • ψ with hζ₀def
    have hζ₀span : ζ₀ ∈ zSpan (L := ↥L) S :=
      sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span hχ))
        (Submodule.smul_mem _ _ (Submodule.subset_span hψ))
    have hζ₀1 : ζ₀ 1 = 0 := by
      rw [hζ₀def]
      simp only [ClassFunction.sub_apply, ClassFunction.zsmul_apply,
        hd1 χ hχ, hd1 ψ hψ, zsmul_eq_mul]
      push_cast
      ring
    have h := hcomm ζ₀ hζ₀span hζ₀1
    have hL : ClassFunction.mapRingEquiv σc (τ₁ ζ₀) =
        ε χ hχ • ((d ψ hψ : ℤ) •
            (IrreducibleCharacter.galoisMap σc (ξ χ hχ) : ClassFunction G ℂ)
          - (d χ hχ : ℤ) •
            (IrreducibleCharacter.galoisMap σc (ξ ψ hψ) : ClassFunction G ℂ)) := by
      rw [hζ₀def, map_sub, map_smul, map_smul, ClassFunction.mapRingEquiv_sub,
        ClassFunction.mapRingEquiv_zsmul, ClassFunction.mapRingEquiv_zsmul, huτχ, huτψ,
        smul_sub, smul_comm (ε χ hχ) ((d ψ hψ : ℤ)), smul_comm (ε χ hχ) ((d χ hχ : ℤ))]
    have hR : τ₁ (ClassFunction.mapRingEquiv σc ζ₀) =
        ε χ hχ • ((d ψ hψ : ℤ) • (ξ _ hχu : ClassFunction G ℂ)
          - (d χ hχ : ℤ) • (ξ _ hψu : ClassFunction G ℂ)) := by
      rw [hζ₀def, ClassFunction.mapRingEquiv_sub, ClassFunction.mapRingEquiv_zsmul,
        ClassFunction.mapRingEquiv_zsmul, map_sub, map_smul, map_smul, hτuχ, hτuψ,
        smul_sub, smul_comm (ε χ hχ) ((d ψ hψ : ℤ)), smul_comm (ε χ hχ) ((d χ hχ : ℤ))]
    rw [hL, hR] at h
    have h' := congrArg (fun x => ε χ hχ • x) h
    simpa only [smul_smul, hE2, one_smul] using h'
  -- (vi) the second constituent differs from the first
  have hτne : τ₁ ψ ≠ τ₁ χ := by
    intro heq
    have hiso := hτ.extension_inner_eq (ψ - χ) (ψ - χ)
      (sub_mem (Submodule.subset_span hψ) (Submodule.subset_span hχ))
      (sub_mem (Submodule.subset_span hψ) (Submodule.subset_span hχ))
    rw [map_sub, heq, sub_self] at hiso
    have hzero : ClassFunction.inner (0 : ClassFunction G ℂ) (0 : ClassFunction G ℂ) = 0 := by
      rw [show (0 : ClassFunction G ℂ) = (0 : ℂ) • (0 : ClassFunction G ℂ) from
        (zero_smul ℂ _).symm, ClassFunction.inner_smul_left, zero_mul]
    rw [hzero] at hiso
    have hψχ' : (⟨ψ, hSirr hψ⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hSirr hχ⟩ := by
      intro h
      exact hψχ (congrArg (fun ξ' : IrreducibleCharacter ↥L => (ξ' : ClassFunction ↥L ℂ)) h)
    have h11 := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hSirr hψ⟩ : IrreducibleCharacter ↥L) (⟨ψ, hSirr hψ⟩ : IrreducibleCharacter ↥L)
    have h22 := irreducibleCharacter_inner_eq_ite
      (⟨χ, hSirr hχ⟩ : IrreducibleCharacter ↥L) (⟨χ, hSirr hχ⟩ : IrreducibleCharacter ↥L)
    have h12 := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hSirr hψ⟩ : IrreducibleCharacter ↥L) (⟨χ, hSirr hχ⟩ : IrreducibleCharacter ↥L)
    have h21 := irreducibleCharacter_inner_eq_ite
      (⟨χ, hSirr hχ⟩ : IrreducibleCharacter ↥L) (⟨ψ, hSirr hψ⟩ : IrreducibleCharacter ↥L)
    rw [if_pos rfl] at h11 h22
    rw [if_neg hψχ'] at h12
    rw [if_neg (Ne.symm hψχ')] at h21
    have htwo : ClassFunction.inner (ψ - χ) (ψ - χ) = 2 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h11, h22, h12, h21]
      ring
    rw [htwo] at hiso
    exact two_ne_zero hiso.symm
  have hB21 : IrreducibleCharacter.galoisMap σc (ξ ψ hψ) ≠
      IrreducibleCharacter.galoisMap σc (ξ χ hχ) := by
    intro h
    have hξne : ξ ψ hψ = ξ χ hχ := by
      have hinj : Function.Injective (IrreducibleCharacter.galoisMap (G := G) σc) := by
        intro x y hxy
        have := congrArg (IrreducibleCharacter.galoisMap σc.symm) hxy
        simpa using this
      exact hinj h
    refine hτne ?_
    rw [hξrepr ψ hψ, hξrepr χ hχ, hsign ψ hψ χ hχ, hξne]
  -- (vii) compare the coefficient of `(ξ_χ)^{σc}` in the main equation
  have hexp : ∀ (n m : ℕ) (X Y : IrreducibleCharacter G),
      ClassFunction.inner
          ((n : ℤ) • (X : ClassFunction G ℂ) - (m : ℤ) • (Y : ClassFunction G ℂ))
          (IrreducibleCharacter.galoisMap σc (ξ χ hχ) : ClassFunction G ℂ) =
        (n : ℂ) * (if X = IrreducibleCharacter.galoisMap σc (ξ χ hχ) then 1 else 0)
          - (m : ℂ) * (if Y = IrreducibleCharacter.galoisMap σc (ξ χ hχ) then 1 else 0) := by
    intro n m X Y
    rw [ClassFunction.inner_sub_left, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
      irreducibleCharacter_inner_eq_ite X (IrreducibleCharacter.galoisMap σc (ξ χ hχ)),
      irreducibleCharacter_inner_eq_ite Y (IrreducibleCharacter.galoisMap σc (ξ χ hχ))]
    push_cast
    ring
  have hcmp := congrArg
    (fun x : ClassFunction G ℂ =>
      ClassFunction.inner x (IrreducibleCharacter.galoisMap σc (ξ χ hχ) : ClassFunction G ℂ))
    hmain
  simp only [hexp (d ψ hψ) (d χ hχ)] at hcmp
  rw [if_neg hB21] at hcmp
  simp only [if_true] at hcmp
  -- conclude: the goal reduces to `ξ_{χ^{σc}} = (ξ_χ)^{σc}`
  by_cases h31 : ξ _ hχu = IrreducibleCharacter.galoisMap σc (ξ χ hχ)
  · rw [huτχ, hτuχ, h31]
  · exfalso
    rw [if_neg h31] at hcmp
    by_cases h41 : ξ _ hψu = IrreducibleCharacter.galoisMap σc (ξ χ hχ)
    · rw [if_pos h41] at hcmp
      have hsum : ((d ψ hψ + d χ hχ : ℕ) : ℂ) = 0 := by
        push_cast
        linear_combination hcmp
      have h0 : d ψ hψ + d χ hχ = 0 := Nat.cast_eq_zero.mp hsum
      have := hdpos ψ hψ
      omega
    · rw [if_neg h41] at hcmp
      have hsum : ((d ψ hψ : ℕ) : ℂ) = 0 := by
        linear_combination hcmp
      have h0 : d ψ hψ = 0 := Nat.cast_eq_zero.mp hsum
      have := hdpos ψ hψ
      omega

/-- **Peterfalvi (6.8.2.1), core step.**  In the (5.9.a) situation, let `η ∈ S` take its
degree value at some `x ∈ L` with `(x : G) ∈ A` (in the application `x ∈ Z ⊆ H' ⊆ Ker η`),
and let `σc` act as `(· ^ k)` on `orderOf (x : G)`-th roots of unity (supplied by (1.9.b)
via `exists_complexRingEquiv_pow_and_fixed`).  Then the coherent extension satisfies

`(τ₁ η)((x : G) ^ k) = (τ₁ η)(x : G)`.

Chain: `(τ₁η)(x^k) = (τ₁η)^{σc}(x)` by the (1.9.b) value formula (`τ₁η ∈ ℤ[Irr G]`);
`(τ₁η)^{σc} = τ₁(η^{σc})` by (5.9.a); and `η^{σc} − η` vanishes at `1` (degrees are
rationals, fixed by `σc`), hence is supported on `A'` and `τ₁ = τ` there, so its value at
`x ∈ A` is restored by the Dade map: `(τ(η^{σc} − η))(x) = (η^{σc} − η)(x) = 0` since
`η(x) = η(1)` is rational.  This is the engine behind "`η^{τ₁}` is constant on `Z^#`"
((6.8.2.1), mmd 04.8 L182-184). -/
theorem IsCoherent.extension_apply_coe_pow_eq
    {hyp : S04.Hypothesis G A L} {dade : S04.FullDadeIsometryData (G := G) hyp}
    {S : Set (ClassFunction (↥L) ℂ)} {A' : Set ↥L}
    (hτ : IsCoherent (dadeIntegralCharacterMap hyp dade) S A')
    (hA' : A' ⊆ supportInSubgroup A L)
    (hSirr : S ⊆ irreducibleCharacters ↥L)
    (hspan : ∀ φ ∈ zSpan (L := ↥L) S, φ 1 = 0 → φ.support ⊆ A')
    (σc : ℂ ≃+* ℂ) (hSu : ∀ φ ∈ S, ClassFunction.mapRingEquiv σc φ ∈ S)
    (hlat : ∀ φ ∈ S, hτ.extension φ ∈ ZIrr G)
    {η : ClassFunction (↥L) ℂ} (hη : η ∈ S) (hpair : ∃ ψ ∈ S, ψ ≠ η)
    {x : ↥L} (hxA : (x : G) ∈ A) (hηx : η x = η 1)
    {k : ℕ} (hσpow : ∀ ζ : ℂ, ζ ^ orderOf ((x : G)) = 1 → σc ζ = ζ ^ k) :
    hτ.extension η ((x : G) ^ k) = hτ.extension η (x : G) := by
  classical
  -- the degree `η 1` is a natural number, hence fixed by `σc`
  obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
    (⟨η, hSirr hη⟩ : IrreducibleCharacter ↥L)
  have hσ1 : σc (η 1) = η 1 := by rw [hd, map_natCast]
  -- (1.9.b) value formula for the virtual character `τ₁ η ∈ ℤ[Irr G]`
  have h1 : ClassFunction.mapRingEquiv σc (hτ.extension η) (x : G) =
      hτ.extension η (((x : G)) ^ k) :=
    mapRingEquiv_apply_eq_apply_pow_of_mem_ZIrr (hlat η hη) σc
      (isOfFinOrder_of_finite _) hσpow
  -- (5.9.a): the extension commutes with `σc` on `S`
  have hcomm := hτ.extension_mapRingEquiv_comm hA' hSirr hspan σc hSu hlat hη hpair
  -- the difference `δ = η^{σc} − η` is supported and its Dade image vanishes at `x`
  set δ : ClassFunction (↥L) ℂ := ClassFunction.mapRingEquiv σc η - η with hδdef
  have hδspan : δ ∈ zSpan (L := ↥L) S :=
    sub_mem (Submodule.subset_span (hSu η hη)) (Submodule.subset_span hη)
  have hδ1 : δ 1 = 0 := by
    rw [hδdef]
    simp only [ClassFunction.sub_apply, ClassFunction.mapRingEquiv_apply, hσ1, sub_self]
  have hδsupp : δ.support ⊆ A' := hspan δ hδspan hδ1
  have hτδx : hτ.extension δ (x : G) = 0 := by
    rw [hτ.extends_on_supported δ ⟨hδspan, hδsupp⟩,
      dadeIntegralCharacterMap_apply_mem hyp dade (hδsupp.trans hA') hxA]
    rw [hδdef]
    simp only [ClassFunction.sub_apply, ClassFunction.mapRingEquiv_apply]
    rw [show ((⟨(x : G), hyp.mem_L hxA⟩ : ↥L)) = x from rfl, hηx, hσ1, sub_self]
  -- assemble
  have hsplit : hτ.extension (ClassFunction.mapRingEquiv σc η) =
      hτ.extension η + hτ.extension δ := by
    rw [hδdef, map_sub]
    abel
  calc hτ.extension η ((x : G) ^ k)
      = ClassFunction.mapRingEquiv σc (hτ.extension η) (x : G) := h1.symm
    _ = hτ.extension (ClassFunction.mapRingEquiv σc η) (x : G) := by rw [hcomm]
    _ = hτ.extension η (x : G) + hτ.extension δ (x : G) := by
        rw [hsplit]
        rfl
    _ = hτ.extension η (x : G) := by rw [hτδx, add_zero]

/-- **Peterfalvi (6.8.2.1)** (generic Z^#-constancy form).  Let `Z ≤ L` have prime order
with `Z^# ⊆ A` (coe to `G`), and let `η ∈ S` take its degree value on `Z` (in the
application `Z ⊆ H' ⊆ Ker η`).  If `S` is closed under all coefficientwise automorphisms,
then the coherent extension `τ₁ η` is **constant on `Z^#`**: for `x, y ∈ Z^#`,
`(τ₁ η)(y) = (τ₁ η)(x)`.

The required automorphism is produced by (1.9): writing `|G| = w₂^e · m` with `w₂ ∤ m`
(`Nat.exists_eq_pow_mul_and_not_dvd`), `exists_complexRingEquiv_pow_and_fixed` provides
`σ` acting as `(· ^ k)` on `w₂^e`-th roots of unity, and `y = x^k` since `x` generates the
prime-order `Z`. -/
theorem IsCoherent.extension_constant_on_sharp_of_prime
    {hyp : S04.Hypothesis G A L} {dade : S04.FullDadeIsometryData (G := G) hyp}
    {S : Set (ClassFunction (↥L) ℂ)} {A' : Set ↥L}
    (hτ : IsCoherent (dadeIntegralCharacterMap hyp dade) S A')
    (hA' : A' ⊆ supportInSubgroup A L)
    (hSirr : S ⊆ irreducibleCharacters ↥L)
    (hspan : ∀ φ ∈ zSpan (L := ↥L) S, φ 1 = 0 → φ.support ⊆ A')
    (hSu : ∀ σc : ℂ ≃+* ℂ, ∀ φ ∈ S, ClassFunction.mapRingEquiv σc φ ∈ S)
    (hlat : ∀ φ ∈ S, hτ.extension φ ∈ ZIrr G)
    {η : ClassFunction (↥L) ℂ} (hη : η ∈ S) (hpair : ∃ ψ ∈ S, ψ ≠ η)
    {Z : Subgroup ↥L} (hZp : (Nat.card Z).Prime)
    (hZA : ∀ ⦃z : ↥L⦄, z ∈ Z → z ≠ 1 → (z : G) ∈ A)
    {x : ↥L} (hx : x ∈ Z) (hx1 : x ≠ 1) (hηx : η x = η 1)
    {y : ↥L} (hy : y ∈ Z) (hy1 : y ≠ 1) :
    hτ.extension η (y : G) = hτ.extension η (x : G) := by
  classical
  set w₂ : ℕ := Nat.card ↥Z with hw₂
  have : Finite ↥Z := Subtype.finite
  -- `x` has order `w₂` and generates `Z`
  have hordx' : orderOf (⟨x, hx⟩ : ↥Z) = w₂ := by
    rcases (Nat.dvd_prime hZp).mp (orderOf_dvd_natCard (⟨x, hx⟩ : ↥Z)) with h | h
    · exfalso
      exact hx1 (congrArg (Subtype.val : ↥Z → ↥L) (orderOf_eq_one_iff.mp h))
    · exact h
  have hgen : (⟨y, hy⟩ : ↥Z) ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Z) := by
    have htop : Subgroup.zpowers (⟨x, hx⟩ : ↥Z) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hordx', hw₂]
    rw [htop]
    trivial
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr hgen :
    (⟨y, hy⟩ : ↥Z) ∈ Submonoid.powers (⟨x, hx⟩ : ↥Z))
  replace hk : (⟨x, hx⟩ : ↥Z) ^ k = (⟨y, hy⟩ : ↥Z) := hk
  -- normalize the exponent to `0 < k' < w₂`
  set k' : ℕ := k % w₂ with hk'def
  have hk'eq : (⟨x, hx⟩ : ↥Z) ^ k' = (⟨y, hy⟩ : ↥Z) := by
    rw [hk'def, ← hordx', pow_mod_orderOf, hk]
  have hk'lt : k' < w₂ := Nat.mod_lt _ hZp.pos
  have hk'ne : k' ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk'eq
    exact hy1 (congrArg (Subtype.val : ↥Z → ↥L) hk'eq.symm)
  have hkcop : k'.Coprime w₂ :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hZp).mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk'ne) hk'lt)))
  -- the coe relation `y = x^{k'}` in `G`
  have hyL : x ^ k' = y := by
    have h := congrArg (Subtype.val : ↥Z → ↥L) hk'eq
    rwa [SubmonoidClass.coe_pow] at h
  have hyx : (y : G) = ((x : G)) ^ k' := by
    rw [← hyL, SubmonoidClass.coe_pow]
  -- the order of `(x : G)` is `w₂`
  have hordG : orderOf ((x : G)) = w₂ := by
    have h1 : orderOf ((x : G)) = orderOf x :=
      orderOf_injective L.subtype Subtype.val_injective x
    have h2 : orderOf x = orderOf (⟨x, hx⟩ : ↥Z) :=
      orderOf_injective Z.subtype Subtype.val_injective ⟨x, hx⟩
    rw [h1, h2, hordx']
  -- (1.9): the automorphism acting as `(· ^ k')` on `w₂`-power roots of unity
  obtain ⟨e, m, hmnd, hGem⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.card_pos (α := G)).ne' w₂ hZp.one_lt.ne'
  have hw₂G : w₂ ∣ Nat.card G := by
    rw [← hordG]
    exact orderOf_dvd_natCard _
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_mul] at hGem
    exact hmnd (hGem ▸ hw₂G)
  have ha : w₂ ^ e ≠ 0 := pow_ne_zero _ hZp.pos.ne'
  have hm : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hGem
    exact (Nat.card_pos (α := G)).ne' hGem
  have hab : (w₂ ^ e).Coprime m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hZp).mpr hmnd)
  have hka : k'.Coprime (w₂ ^ e) := Nat.Coprime.pow_right _ hkcop
  obtain ⟨σc, hσa, _⟩ := exists_complexRingEquiv_pow_and_fixed ha hm hab hka
  -- apply the core step
  rw [hyx]
  exact hτ.extension_apply_coe_pow_eq hA' hSirr hspan σc (hSu σc) hlat hη hpair
    (hZA hx hx1) hηx
    (fun ζ hζ => hσa ζ (by
      rw [hordG] at hζ
      have hee : e - 1 + 1 = e := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero he0)
      have hpow : ζ ^ (w₂ ^ e) = (ζ ^ w₂) ^ (w₂ ^ (e - 1)) := by
        rw [← pow_mul, ← pow_succ', hee]
      rw [hpow, hζ, one_pow]))

end OddOrder.Peterfalvi.S07


