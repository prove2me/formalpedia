-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_RetargetScaled
-- name    : OddOrder_Peterfalvi_S07_RetargetScaled
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:05:53.051172+00:00
-- url     : https://prove2.me/theorems/196ae3c0-5bd5-4077-9c5e-3f589679261b
-- title:
--   Peterfalvi (5.6.3): re-targeting for a non-orthonormal (reducible) break character
-- statement:
--   The earlier `retarget` machinery builds the (5.6.3) coherence extension for an orthonormal break pair $\{\chi,\bar\chi\}$ with $\|\chi\|^2=1$, where the Gram–Schmidt projection uses $\langle\varphi,\chi\rangle$ directly. This file handles a reducible break character, using the norm-scaled projection coefficients.
--
--   Main definitions: `orthoResidualMapS` (the scaled Gram–Schmidt residual map), `retargetS` (the scaled rank-2 re-targeting of an integral map) and `retarget_isCoherent_S` (coherence of $S_1\cup\{\chi,\bar\chi\}$ for a reducible break $\chi$).
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_RetargetScaled.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_RetargetScaled.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_DifferenceImage
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_NormInequalities
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_FamilyBundleDade

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

open IntegralCharacterMap

open CharacterPsiDecomposition

variable {L G : Type*} [Group L] [Group G]

variable [Fintype L] [Invertible (Nat.card L : ℂ)]

/-- **Block expansion of a sesquilinear inner product, variable norms.**
The `‖e‖² = ee`, `‖f‖² = ff` generalization of `inner_block_expand`: for `u, u'` each orthogonal to
`e` and `f`, and `⟨e,f⟩ = ⟨f,e⟩ = 0`,
`⟨u + s·e + t·f, u' + s'·e + t'·f⟩ = ⟨u,u'⟩ + s·s̄'·ee + t·t̄'·ff`. -/
theorem inner_block_expand_gen {W : Type*} [Group W] [Fintype W] [Invertible (Nat.card W : ℂ)]
    {e f u u' : ClassFunction W ℂ} {s t s' t' ee ff : ℂ}
    (hee : ClassFunction.inner e e = ee) (hff : ClassFunction.inner f f = ff)
    (hef : ClassFunction.inner e f = 0) (hfe : ClassFunction.inner f e = 0)
    (hue : ClassFunction.inner u e = 0) (huf : ClassFunction.inner u f = 0)
    (hu'e : ClassFunction.inner u' e = 0) (hu'f : ClassFunction.inner u' f = 0) :
    ClassFunction.inner (u + s • e + t • f) (u' + s' • e + t' • f) =
      ClassFunction.inner u u' + s * star s' * ee + t * star t' * ff := by
  have heu' : ClassFunction.inner e u' = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hu'e, star_zero]
  have hfu' : ClassFunction.inner f u' = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hu'f, star_zero]
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    hue, huf, heu', hfu', hee, hff, hef, hfe]
  ring

/-- The **scaled** Gram–Schmidt residual map `φ ↦ φ − (⟨φ,χ⟩/‖χ‖²)·χ − (⟨φ,χ̄⟩/‖χ̄‖²)·χ̄`.
Generalizes `orthoResidualMap` (recovered when `‖χ‖² = ‖χ̄‖² = 1`); remains `ℤ`-linear because the
`(⟨χ,χ⟩)⁻¹` factor lands in the `ℂ`-valued target of the `ℤ`-linear functional `innerLeftℤ χ`. -/
noncomputable def orthoResidualMapS (χ chibar : ClassFunction L ℂ) :
    ClassFunction L ℂ →ₗ[ℤ] ClassFunction L ℂ :=
  LinearMap.id - (innerLeftℤ (L := L) χ).smulRight ((ClassFunction.inner χ χ)⁻¹ • χ)
    - (innerLeftℤ (L := L) chibar).smulRight ((ClassFunction.inner chibar chibar)⁻¹ • chibar)

@[simp] theorem orthoResidualMapS_apply (χ chibar φ : ClassFunction L ℂ) :
    orthoResidualMapS (L := L) χ chibar φ =
      φ - ClassFunction.inner φ χ • ((ClassFunction.inner χ χ)⁻¹ • χ)
        - ClassFunction.inner φ chibar • ((ClassFunction.inner chibar chibar)⁻¹ • chibar) := by
  simp [orthoResidualMapS, LinearMap.smulRight_apply]

/-- The scaled residual `φ⊥` is orthogonal to `χ` (using `‖χ‖² ≠ 0` and `⟨χ̄,χ⟩ = 0`). -/
theorem inner_orthoResidualMapS_left {χ chibar : ClassFunction L ℂ}
    (hχχne : ClassFunction.inner χ χ ≠ 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (φ : ClassFunction L ℂ) :
    ClassFunction.inner (orthoResidualMapS (L := L) χ chibar φ) χ = 0 := by
  simp only [orthoResidualMapS_apply, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left]
  rw [hχbarχ, mul_zero, mul_zero, sub_zero, inv_mul_cancel₀ hχχne, mul_one, sub_self]

/-- The scaled residual `φ⊥` is orthogonal to `χ̄` (using `‖χ̄‖² ≠ 0` and `⟨χ,χ̄⟩ = 0`). -/
theorem inner_orthoResidualMapS_right {χ chibar : ClassFunction L ℂ}
    (hχχbar : ClassFunction.inner χ chibar = 0)
    (hχbarχbarne : ClassFunction.inner chibar chibar ≠ 0)
    (φ : ClassFunction L ℂ) :
    ClassFunction.inner (orthoResidualMapS (L := L) χ chibar φ) chibar = 0 := by
  simp only [orthoResidualMapS_apply, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left]
  rw [hχχbar, mul_zero, mul_zero, sub_zero, inv_mul_cancel₀ hχbarχbarne, mul_one, sub_self]

/-- The scaled rank-`2` **re-targeting** of an integral map `τ₁`:
`φ ↦ τ₁ φ⊥ + (⟨φ,χ⟩/‖χ‖²)·X + (⟨φ,χ̄⟩/‖χ̄‖²)·X̄`.  On the integral lattice `ℤ[S₁ ∪ {χ, χ̄}]`
(`χ ⊥ S₁`, `χ ⊥ χ̄`) it sends `χ ↦ X`, `χ̄ ↦ X̄` and keeps `τ₁` on the residual, with **integer**
coefficients (the projection coordinate). -/
noncomputable def retargetS (τ₁ : IntegralCharacterMap L G)
    (χ chibar : ClassFunction L ℂ) (X Xbar : ClassFunction G ℂ) :
    IntegralCharacterMap L G :=
  τ₁ ∘ₗ orthoResidualMapS (L := L) χ chibar
    + (innerLeftℤ (L := L) χ).smulRight ((ClassFunction.inner χ χ)⁻¹ • X)
    + (innerLeftℤ (L := L) chibar).smulRight ((ClassFunction.inner chibar chibar)⁻¹ • Xbar)

@[simp] theorem retargetS_apply (τ₁ : IntegralCharacterMap L G)
    (χ chibar : ClassFunction L ℂ) (X Xbar : ClassFunction G ℂ) (φ : ClassFunction L ℂ) :
    retargetS τ₁ χ chibar X Xbar φ =
      τ₁ (orthoResidualMapS (L := L) χ chibar φ)
        + ClassFunction.inner φ χ • ((ClassFunction.inner χ χ)⁻¹ • X)
        + ClassFunction.inner φ chibar • ((ClassFunction.inner chibar chibar)⁻¹ • Xbar) := by
  simp [retargetS, LinearMap.smulRight_apply]

/-- The scaled Gram–Schmidt residual carries `ℤ[S₁ ∪ {χ, χ̄}]` into `ℤ[S₁]`
(`orthoResidualMap_mem_zSpan` analogue, `‖χ‖² ≠ 1`).  For `x ∈ S₁` the residual is `x` (since
`x ⊥ {χ, χ̄}`, the scaled coefficients vanish); for `x = χ` (resp. `χ̄`) it is `0`
(`⟨χ,χ⟩·‖χ‖⁻² = 1`); and `orthoResidualMapS` is `ℤ`-linear. -/
theorem orthoResidualMapS_mem_zSpan {χ chibar : ClassFunction L ℂ}
    {S₁ : Set (ClassFunction L ℂ)}
    (hχχne : ClassFunction.inner χ χ ≠ 0) (hχbarχbarne : ClassFunction.inner chibar chibar ≠ 0)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ (S₁ ∪ {χ, chibar})) :
    orthoResidualMapS (L := L) χ chibar φ ∈ Submodule.span ℤ S₁ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      rcases hx with hxS1 | hxpair
      · have hxχ : ClassFunction.inner x χ = 0 := by
          rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 x hxS1, star_zero]
        have hxχbar : ClassFunction.inner x chibar = 0 := by
          rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 x hxS1, star_zero]
        rw [orthoResidualMapS_apply, hxχ, hxχbar, zero_smul, zero_smul, sub_zero, sub_zero]
        exact Submodule.subset_span hxS1
      · rcases hxpair with rfl | rfl
        · rw [orthoResidualMapS_apply, hχχbar, zero_smul, sub_zero, smul_smul,
            mul_inv_cancel₀ hχχne, one_smul, sub_self]
          exact Submodule.zero_mem _
        · rw [orthoResidualMapS_apply, hχbarχ, zero_smul, sub_zero, smul_smul,
            mul_inv_cancel₀ hχbarχbarne, one_smul, sub_self]
          exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ a ih

/-- **The scaled integral-span re-targeting isometry (5.6.3 lattice isometry, reducible break).**
The `‖χ‖² ≠ 1` analogue of `retarget_inner_eq_on_zSpan_union`: re-targeting an isometry `τ₁` (only
required isometric on `ℤ[S₁]`) preserves `⟨·,·⟩` on all of `ℤ[S₁ ∪ {χ, χ̄}]`, with Gram-matching
target `⟨X,X⟩ = ⟨χ,χ⟩`, `⟨X̄,X̄⟩ = ⟨χ̄,χ̄⟩`.  Every scaled residual lands in `ℤ[S₁]`
(`orthoResidualMapS_mem_zSpan`); the block expansion `inner_block_expand_gen` then closes it using
only the `ℤ[S₁]`-isometry of `τ₁` and the lattice orthogonality `X, X̄ ⊥ τ₁(ℤ[S₁])`. -/
theorem retargetS_inner_eq_on_zSpan_union {τ₁ : IntegralCharacterMap L G}
    {χ chibar : ClassFunction L ℂ} {X Xbar : ClassFunction G ℂ}
    {S₁ : Set (ClassFunction L ℂ)} [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hτ₁ : ∀ u v : ClassFunction L ℂ, u ∈ Submodule.span ℤ S₁ → v ∈ Submodule.span ℤ S₁ →
      ClassFunction.inner (τ₁ u) (τ₁ v) = ClassFunction.inner u v)
    (hχχne : ClassFunction.inner χ χ ≠ 0) (hχbarχbarne : ClassFunction.inner chibar chibar ≠ 0)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hXX : ClassFunction.inner X X = ClassFunction.inner χ χ)
    (hXbarXbar : ClassFunction.inner Xbar Xbar = ClassFunction.inner chibar chibar)
    (hXXbar : ClassFunction.inner X Xbar = 0) (hXbarX : ClassFunction.inner Xbar X = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (τ₁ ξ) X = 0)
    (hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (τ₁ ξ) Xbar = 0)
    {φ ψ : ClassFunction L ℂ}
    (hφ : φ ∈ Submodule.span ℤ (S₁ ∪ {χ, chibar}))
    (hψ : ψ ∈ Submodule.span ℤ (S₁ ∪ {χ, chibar})) :
    ClassFunction.inner (retargetS τ₁ χ chibar X Xbar φ) (retargetS τ₁ χ chibar X Xbar ψ) =
      ClassFunction.inner φ ψ := by
  set s := ClassFunction.inner φ χ with hs
  set t := ClassFunction.inner φ chibar with ht
  set s' := ClassFunction.inner ψ χ with hs'
  set t' := ClassFunction.inner ψ chibar with ht'
  set φperp := orthoResidualMapS (L := L) χ chibar φ with hφperp
  set ψperp := orthoResidualMapS (L := L) χ chibar ψ with hψperp
  have hφperpS1 : φperp ∈ Submodule.span ℤ S₁ :=
    orthoResidualMapS_mem_zSpan hχχne hχbarχbarne hχχbar hχbarχ hχ_S1 hχbar_S1 hφ
  have hψperpS1 : ψperp ∈ Submodule.span ℤ S₁ :=
    orthoResidualMapS_mem_zSpan hχχne hχbarχbarne hχχbar hχbarχ hχ_S1 hχbar_S1 hψ
  have hφperp_χ : ClassFunction.inner φperp χ = 0 :=
    inner_orthoResidualMapS_left hχχne hχbarχ φ
  have hφperp_χbar : ClassFunction.inner φperp chibar = 0 :=
    inner_orthoResidualMapS_right hχχbar hχbarχbarne φ
  have hψperp_χ : ClassFunction.inner ψperp χ = 0 :=
    inner_orthoResidualMapS_left hχχne hχbarχ ψ
  have hψperp_χbar : ClassFunction.inner ψperp chibar = 0 :=
    inner_orthoResidualMapS_right hχχbar hχbarχbarne ψ
  have himg : ClassFunction.inner (retargetS τ₁ χ chibar X Xbar φ)
      (retargetS τ₁ χ chibar X Xbar ψ) =
      ClassFunction.inner (τ₁ φperp) (τ₁ ψperp)
        + s * (ClassFunction.inner χ χ)⁻¹ * star (s' * (ClassFunction.inner χ χ)⁻¹)
            * ClassFunction.inner χ χ
        + t * (ClassFunction.inner chibar chibar)⁻¹
            * star (t' * (ClassFunction.inner chibar chibar)⁻¹)
            * ClassFunction.inner chibar chibar := by
    rw [retargetS_apply, retargetS_apply, ← hφperp, ← hψperp, ← hs, ← ht, ← hs', ← ht']
    simp only [smul_smul]
    exact inner_block_expand_gen hXX hXbarXbar hXXbar hXbarX
      (hX_ortho φperp hφperpS1) (hXbar_ortho φperp hφperpS1)
      (hX_ortho ψperp hψperpS1) (hXbar_ortho ψperp hψperpS1)
  have hsrc : ClassFunction.inner φ ψ =
      ClassFunction.inner φperp ψperp
        + s * (ClassFunction.inner χ χ)⁻¹ * star (s' * (ClassFunction.inner χ χ)⁻¹)
            * ClassFunction.inner χ χ
        + t * (ClassFunction.inner chibar chibar)⁻¹
            * star (t' * (ClassFunction.inner chibar chibar)⁻¹)
            * ClassFunction.inner chibar chibar := by
    have hφ' : φ = φperp + (s * (ClassFunction.inner χ χ)⁻¹) • χ
        + (t * (ClassFunction.inner chibar chibar)⁻¹) • chibar := by
      rw [hφperp, orthoResidualMapS_apply, ← hs, ← ht, smul_smul, smul_smul]; abel
    have hψ' : ψ = ψperp + (s' * (ClassFunction.inner χ χ)⁻¹) • χ
        + (t' * (ClassFunction.inner chibar chibar)⁻¹) • chibar := by
      rw [hψperp, orthoResidualMapS_apply, ← hs', ← ht', smul_smul, smul_smul]; abel
    rw [hφ', hψ']
    exact inner_block_expand_gen rfl rfl hχχbar hχbarχ
      hφperp_χ hφperp_χbar hψperp_χ hψperp_χbar
  rw [himg, hsrc, hτ₁ φperp ψperp hφperpS1 hψperpS1]

section Apply

variable {τ₁ : IntegralCharacterMap L G} {χ chibar : ClassFunction L ℂ} {X Xbar : ClassFunction G ℂ}

/-- On the orthogonal complement of `{χ, χ̄}` the scaled re-targeting agrees with `τ₁`. -/
theorem retargetS_eq_of_orthogonal {φ : ClassFunction L ℂ}
    (hφχ : ClassFunction.inner φ χ = 0) (hφχbar : ClassFunction.inner φ chibar = 0) :
    retargetS τ₁ χ chibar X Xbar φ = τ₁ φ := by
  have hres : orthoResidualMapS (L := L) χ chibar φ = φ := by
    rw [orthoResidualMapS_apply, hφχ, hφχbar, zero_smul, zero_smul, sub_zero, sub_zero]
  rw [retargetS_apply, hres, hφχ, hφχbar, zero_smul, zero_smul, add_zero, add_zero]

/-- `χ ↦ X` for the scaled re-targeting (`‖χ‖² ≠ 0`, `⟨χ,χ̄⟩ = 0`). -/
theorem retargetS_apply_left (hχχne : ClassFunction.inner χ χ ≠ 0)
    (hχχbar : ClassFunction.inner χ chibar = 0) :
    retargetS τ₁ χ chibar X Xbar χ = X := by
  have hres : orthoResidualMapS (L := L) χ chibar χ = 0 := by
    rw [orthoResidualMapS_apply, hχχbar, zero_smul, sub_zero, smul_smul, mul_inv_cancel₀ hχχne,
      one_smul, sub_self]
  rw [retargetS_apply, hres, map_zero, hχχbar, zero_smul, add_zero, zero_add, smul_smul,
    mul_inv_cancel₀ hχχne, one_smul]

/-- `χ̄ ↦ X̄` for the scaled re-targeting (`‖χ̄‖² ≠ 0`, `⟨χ̄,χ⟩ = 0`). -/
theorem retargetS_apply_right (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hχbarχbarne : ClassFunction.inner chibar chibar ≠ 0) :
    retargetS τ₁ χ chibar X Xbar chibar = Xbar := by
  have hres : orthoResidualMapS (L := L) χ chibar chibar = 0 := by
    rw [orthoResidualMapS_apply, hχbarχ, zero_smul, sub_zero, smul_smul,
      mul_inv_cancel₀ hχbarχbarne,
      one_smul, sub_self]
  rw [retargetS_apply, hres, map_zero, hχbarχ, zero_smul, add_zero, zero_add, smul_smul,
    mul_inv_cancel₀ hχbarχbarne, one_smul]

end Apply

/-- **Peterfalvi (5.6.3): coherence of `S₁ ∪ {χ, χ̄}` for a reducible break `χ`.**

The `‖χ‖² ≠ 1` analogue of `retarget_isCoherent`.  Given a coherent `τ` on `S₁`
(`τ₁ := hS₁.extension`), a conjugate pair `{χ, χ̄}` disjoint from and orthogonal to `S₁` with
`‖χ‖² ≠ 0`, `‖χ̄‖² ≠ 0`, and the (5.4)/(5.5)/(5.6.2) target data `{X, X̄} ⊂ ℤ[Irr G]` with
**matching
Gram** `⟨X,X⟩ = ⟨χ,χ⟩`, `⟨X̄,X̄⟩ = ⟨χ̄,χ̄⟩` (and `X̄ = X − (χ−χ̄)^τ`, both `⊥ τ₁(ℤ[S₁])`, plus the
(5.6.2) image equation), the union `S₁ ∪ {χ, χ̄}` is coherent.

The constructed extension is `τ₂ := retargetS τ₁ χ χ̄ X X̄`: a lattice isometry on `ℤ[S₁ ∪ {χ, χ̄}]`
by `retargetS_inner_eq_on_zSpan_union`, sending `χ ↦ X`, `χ̄ ↦ X̄`, keeping `τ₁` off `{χ, χ̄}`, and
agreeing with `τ` on the supported span via the three difference generators. -/
noncomputable def retarget_isCoherent_S
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ chibar chi1 : ClassFunction L ℂ} {a : ℕ} {X Xbar : ClassFunction G ℂ}
    (hχχne : ClassFunction.inner χ χ ≠ 0) (hχbarχbarne : ClassFunction.inner chibar chibar ≠ 0)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hXX : ClassFunction.inner X X = ClassFunction.inner χ χ)
    (hXbarXbar : ClassFunction.inner Xbar Xbar = ClassFunction.inner chibar chibar)
    (hXXbar : ClassFunction.inner X Xbar = 0) (hXbarX : ClassFunction.inner Xbar X = 0)
    (hXZ : X ∈ ZIrr G) (hXbarZ : Xbar ∈ ZIrr G)
    (hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) X = 0)
    (hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) Xbar = 0)
    (hXbar_def : Xbar = X - τ (χ - chibar))
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hchi1 : chi1 ∈ S₁)
    (himg : τ (χ - a • chi1) = X - a • hS₁.extension chi1)
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, chibar}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1})) :
    IsCoherent τ (S₁ ∪ {χ, chibar}) A := by
  classical
  set τ₁ := hS₁.extension with hτ₁def
  set τ₂ := retargetS τ₁ χ chibar X Xbar with hτ₂def
  have hχ_zspan : ∀ φ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ S₁ →
      ClassFunction.inner χ φ = 0 := fun φ hφ =>
    IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hφ
  have hχbar_zspan : ∀ φ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ S₁ →
      ClassFunction.inner chibar φ = 0 := fun φ hφ =>
    IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχbar_S1 hφ
  have hτ₂_inner : ∀ φ ψ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) (S₁ ∪ {χ, chibar}) → ψ ∈ zSpan (L := L) (S₁ ∪ {χ, chibar}) →
      ClassFunction.inner (τ₂ φ) (τ₂ ψ) = ClassFunction.inner φ ψ := by
    intro φ ψ hφ hψ
    rw [hτ₂def]
    exact retargetS_inner_eq_on_zSpan_union hS₁.extension_inner_eq hχχne hχbarχbarne hχχbar hχbarχ
      hXX hXbarXbar hXXbar hXbarX hχ_S1 hχbar_S1 hX_ortho hXbar_ortho hφ hψ
  have hagree_diff : τ₂ (χ - chibar) = τ (χ - chibar) := by
    rw [hτ₂def, map_sub, retargetS_apply_left hχχne hχχbar,
      retargetS_apply_right hχbarχ hχbarχbarne, hXbar_def]; abel
  have hagree_ratio : τ₂ (χ - a • chi1) = τ (χ - a • chi1) := by
    have hχ₁ : τ₂ chi1 = τ₁ chi1 :=
      retargetS_eq_of_orthogonal
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 chi1 hchi1, star_zero])
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 chi1 hchi1, star_zero])
    rw [hτ₂def, map_sub, map_nsmul, retargetS_apply_left hχχne hχχbar, ← hτ₂def, hχ₁,
      himg, hτ₁def]
  have hagree_S1 : ∀ x ∈ zSupportedSpan (L := L) S₁ A, τ₂ x = τ x := by
    intro x hx
    have hxspan : x ∈ Submodule.span ℤ S₁ := hx.1
    have hτ₂x : τ₂ x = τ₁ x := by
      rw [hτ₂def]
      exact retargetS_eq_of_orthogonal
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_zspan x hxspan, star_zero])
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_zspan x hxspan, star_zero])
    rw [hτ₂x, hτ₁def, hS₁.extends_on_supported x hx]
  have hagree_T : ∀ y ∈ zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1},
      τ₂ y = τ y := by
    intro y hy
    rcases hy with hyS1 | hypair
    · exact hagree_S1 y hyS1
    · rcases hypair with hy1 | hy2
      · rw [hy1]; exact hagree_diff
      · rw [hy2]; exact hagree_ratio
  refine ⟨?_, τ₂, hτ₂_inner, ?_, ?_⟩
  · obtain ⟨φ, hφmem, hφne⟩ := hS₁.nonzero
    exact ⟨φ, zSupportedSpan_mono_left (Set.subset_union_left) hφmem, hφne⟩
  · intro φ hφ
    exact IntegralCharacterMap.eq_on_zSpan_of_eq_on hagree_T (hgen hφ)
  · intro φ hφ
    rw [hτ₂def]
    induction hφ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hyS1 | hyχ
        · rw [retargetS_eq_of_orthogonal
              (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 y hyS1, star_zero])
              (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 y hyS1, star_zero]),
            hτ₁def]
          exact hS₁.extension_mem_ZIrr y (Submodule.subset_span hyS1)
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hyχ
          rcases hyχ with rfl | rfl
          · rw [retargetS_apply_left hχχne hχχbar]; exact hXZ
          · rw [retargetS_apply_right hχbarχ hχbarχbarne]; exact hXbarZ
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul a y _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ a ih

end OddOrder.Peterfalvi.S07


