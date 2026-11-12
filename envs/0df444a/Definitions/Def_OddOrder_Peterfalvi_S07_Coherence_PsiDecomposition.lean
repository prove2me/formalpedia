-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
-- name    : OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:51:22.170403+00:00
-- url     : https://prove2.me/theorems/0a519bb5-b79b-4d5f-b9fd-20a6d0049e30
-- title:
--   Peterfalvi (5.6.3) preparation: $\psi=0$ decomposition and the re-targeting keystone
-- statement:
--   Preparation for Peterfalvi (5.6.3): the $\psi=0$ decomposition, the isometry re-targeting keystone, and (1.1)+(1.4). Includes the (5.6.2) quadratic bound and the capstone $\lambda=0$ and $Z=0$.
--
--   Main definitions: `sum_sq_mul_add_normSq_Z_le` (the (5.6.2) quadratic bound), `lambda_eq_zero_and_Z_eq_zero`, `innerLeftℤ` (the integral-linear functional $\varphi\mapsto\langle\varphi,\eta\rangle$), `orthoResidualMap` (the Gram–Schmidt residual against $\{\chi,\bar\chi\}$), `retarget` (the rank-2 re-targeting of an integral isometry $\tau_1$) and `eq_on_zSpan_of_eq_on` (integral character maps agreeing on a set agree on its span).
--
--   The bundle also proves 28 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_Coherence/PsiDecomposition.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_Coherence/PsiDecomposition.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_NormInequalities

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

namespace CharacterPsiDecomposition

open OddOrder.RepresentationTheory

variable {τ : IntegralCharacterMap L G} {χ ψ : ClassFunction L ℂ}

variable [Fintype L] [Fintype G]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- **Peterfalvi (5.6.2) quadratic bound.**  Suppose the orthogonal part `Y` of the (5.4)
decomposition is written against an **orthogonal family** `v : ι → CF(G)` (indexed over
`s`, with real gram `⟨v i, v j⟩ = if i = j then m i else 0`) plus a residual `Z` orthogonal
to the family, with real coefficients `c`:

`Y = (∑ i ∈ s, (c i) • v i) + Z`.

Then `∑ i ∈ s, (c i)² · m i + ‖Z‖² ≤ ‖ψ‖²`.

This is the geometric half of (5.6.2): the Pythagoras expansion of `‖Y‖²` against the
orthogonal family, combined with the opening bound `‖Y‖² ≤ ‖ψ‖²`
(`inner_self_Y_re_le_inner_self_psi`).
The arithmetic half — substituting the (5.6.1) coefficients and forcing the integer `λ = 0` —
is `int_eq_zero_of_sq_mul_le_of_two_mul_lt`. -/
theorem sum_sq_mul_add_normSq_Z_le
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    {ι : Type*} (s : Finset ι) (v : ι → ClassFunction G ℂ) (c m : ι → ℝ)
    (Z : ClassFunction G ℂ)
    (hY : D.Y = (∑ i ∈ s, (c i : ℂ) • v i) + Z)
    (horth : ∀ i ∈ s, ∀ j ∈ s, ClassFunction.inner (v i) (v j) =
      if i = j then (m i : ℂ) else 0)
    (hZ : ∀ i ∈ s, ClassFunction.inner Z (v i) = 0) :
    (∑ i ∈ s, (c i) ^ 2 * m i) + (ClassFunction.inner Z Z).re ≤
      (ClassFunction.inner ψ ψ).re := by
  have hpyth := inner_self_orthogonalSum_add_re (G := G) s v c m Z horth hZ
  have hYnorm : (ClassFunction.inner D.Y D.Y).re =
      (∑ i ∈ s, (c i) ^ 2 * m i) + (ClassFunction.inner Z Z).re := by
    rw [hY]; exact hpyth
  have hbound := D.inner_self_Y_re_le_inner_self_psi
  rw [hYnorm] at hbound
  exact hbound

open scoped Classical in
/-- **Peterfalvi (5.6.2) capstone: `λ = 0` and `Z = 0`.**

Composes the geometric half (`sum_sq_mul_add_normSq_Z_le`) and the arithmetic half
(`int_eq_zero_of_sq_mul_le_of_two_mul_lt`).  The (5.6.1) decomposition writes the orthogonal
part as

`Y = (∑ i ∈ s, (a·[i = i₁] - λ·r i) • v i) + Z`,

against the orthogonal family `v i` (real gram `m i = ‖χ_i‖²`, `v i = χ_i^{τ₁}`) with `Z`
orthogonal to the family, where `r i = a_i / ‖χ_i‖²`, `i₁` indexes `χ₁`, and `ψ = a·χ₁` (so
`‖ψ‖² = a²·m i₁`, hypothesis `hψ`) with `a₁ = 1` (so `r i₁ · m i₁ = 1`, hypothesis `hr₁`).

The Pythagoras expansion gives `∑ (a·[i=i₁] - λ·r i)²·m i + ‖Z‖² ≤ ‖ψ‖² = a²·m i₁`; the
algebraic identity collapses the left sum to `a²·m i₁ - 2·a·λ + λ²·D` with
`D = ∑ (r i)²·m i`, so `λ²·D - 2·λ·a + ‖Z‖² ≤ 0`.  Hypothesis (c) `2·a < D` then forces
`λ = 0` (`int_eq_zero_of_sq_mul_le_of_two_mul_lt`), and feeding `λ = 0` back gives `‖Z‖² ≤ 0`,
hence `Z = 0` by positive definiteness. -/
theorem lambda_eq_zero_and_Z_eq_zero
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    {ι : Type*} (s : Finset ι) (i₁ : ι) (hi₁ : i₁ ∈ s)
    (a : ℝ) (lam : ℤ) (Z : ClassFunction G ℂ)
    (vc : ι → ClassFunction G ℂ) (mc : ι → ℝ) (rc : ι → ℝ)
    (hY : D.Y = (∑ i ∈ s, ((a * (if i = i₁ then 1 else 0) - (lam : ℝ) * rc i : ℝ) : ℂ) • vc i)
      + Z)
    (horth : ∀ i ∈ s, ∀ j ∈ s, ClassFunction.inner (vc i) (vc j) =
      if i = j then (mc i : ℂ) else 0)
    (hZ : ∀ i ∈ s, ClassFunction.inner Z (vc i) = 0)
    (hψ : (ClassFunction.inner ψ ψ).re = a ^ 2 * mc i₁)
    (hr₁ : rc i₁ * mc i₁ = 1)
    (ha : 0 ≤ a)
    (hD : 2 * a < ∑ i ∈ s, (rc i) ^ 2 * mc i) :
    lam = 0 ∧ Z = 0 := by
  classical
  -- Geometric half: `∑ (c i)²·m i + ‖Z‖² ≤ ‖ψ‖²`.
  have hgeo := D.sum_sq_mul_add_normSq_Z_le s vc
    (fun i => a * (if i = i₁ then 1 else 0) - (lam : ℝ) * rc i) mc Z hY horth hZ
  -- Algebraic collapse of the left sum.
  have halg : (∑ i ∈ s, (a * (if i = i₁ then 1 else 0) - (lam : ℝ) * rc i) ^ 2 * mc i)
      = a ^ 2 * mc i₁ - 2 * a * (lam : ℝ) * (rc i₁ * mc i₁)
        + (lam : ℝ) ^ 2 * ∑ i ∈ s, (rc i) ^ 2 * mc i := by
    have key : ∀ i ∈ s,
        (a * (if i = i₁ then 1 else 0) - (lam : ℝ) * rc i) ^ 2 * mc i
        = (if i = i₁ then (a ^ 2 * mc i₁ - 2 * a * (lam : ℝ) * (rc i₁ * mc i₁)) else 0)
          + (lam : ℝ) ^ 2 * ((rc i) ^ 2 * mc i) := by
      intro i hi
      by_cases h : i = i₁
      · subst h; rw [if_pos rfl, if_pos rfl]; ring
      · rw [if_neg h, if_neg h]; ring
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_ite_eq' s i₁,
      if_pos hi₁, ← Finset.mul_sum]
  -- Substitute `r i₁ · m i₁ = 1` and `‖ψ‖² = a²·m i₁`; obtain the quadratic `≤ 0`.
  set Dsum := ∑ i ∈ s, (rc i) ^ 2 * mc i with hDsum
  have hquad : (lam : ℝ) ^ 2 * Dsum - 2 * (lam : ℝ) * a + (ClassFunction.inner Z Z).re ≤ 0 := by
    rw [halg, hr₁, hψ, mul_one] at hgeo
    nlinarith [hgeo]
  -- Integer forcing (cast to ℚ) gives `λ = 0`.
  have hZre_nonneg : (0 : ℝ) ≤ (ClassFunction.inner Z Z).re := inner_self_re_nonneg Z
  have hlam0 : lam = 0 := by
    -- Work over ℝ directly: the integer-forcing argument transcribed.
    by_contra hne
    rcases lt_trichotomy lam 0 with hneg | hzero | hpos
    · have hlamR : (lam : ℝ) < 0 := by exact_mod_cast hneg
      have hsq_pos : 0 < (lam : ℝ) ^ 2 := by positivity
      have hDpos : 0 < Dsum := by
        have : (0 : ℝ) ≤ 2 * a := by linarith
        linarith [hD]
      nlinarith [mul_pos hsq_pos hDpos, hZre_nonneg, mul_nonneg ha (le_of_lt (neg_pos.mpr hlamR))]
    · exact hne hzero
    · have hlam1 : (1 : ℝ) ≤ (lam : ℝ) := by
        have : (1 : ℤ) ≤ lam := hpos; exact_mod_cast this
      have hlampos : (0 : ℝ) < (lam : ℝ) := by linarith
      -- `λ²·D - 2λa + ‖Z‖² ≤ 0`, `‖Z‖² ≥ 0` ⟹ `λ²·D ≤ 2λa`, cancel `λ` ⟹ `λ·D ≤ 2a < D`.
      have hcore : (lam : ℝ) ^ 2 * Dsum ≤ 2 * (lam : ℝ) * a := by linarith
      have hcancel : (lam : ℝ) * Dsum ≤ 2 * a := by
        have h2 : (lam : ℝ) * ((lam : ℝ) * Dsum) ≤ (lam : ℝ) * (2 * a) := by nlinarith [hcore]
        exact le_of_mul_le_mul_left h2 hlampos
      nlinarith [hcancel, hlam1, hD]
  refine ⟨hlam0, ?_⟩
  -- Feed `λ = 0` back: `‖Z‖² ≤ 0`, hence `Z = 0`.
  have hZ0 : (ClassFunction.inner Z Z).re ≤ 0 := by
    rw [hlam0] at hquad; push_cast at hquad; nlinarith [hquad]
  exact eq_zero_of_inner_self_re_eq_zero (le_antisymm hZ0 hZre_nonneg)

/-- **(5.5) reduction `η ⊥ X`.**  If `η` is orthogonal to every member of `R(χ)`, then `η` is
orthogonal to `X = D.X ∈ ℤ[R(χ)]` (the (5.5) output `X = ∑ coeff•α`).  This is the `hX_ortho` half
of (5.6.3): `⟨η, X⟩ = ∑ coeff·⟨η, α⟩ = 0`. -/
theorem inner_X_eq_zero_of_orthogonal_imageSet
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    {η : ClassFunction G ℂ}
    (hη : ∀ α ∈ D.imageFamily.imageSet, ClassFunction.inner η α = 0) :
    ClassFunction.inner η D.X = 0 := by
  rw [D.X_eq, OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [OddOrder.RepresentationTheory.inner_smul_right, hη α hα, mul_zero]

/-- **Peterfalvi (5.2.e) feed: `X ⊥ R(χ')` from `R(χ) ⊥ R(χ')`.**  The image part `X = D.X ∈
ℤ[R(χ)]` of the (5.4) decomposition for `χ` is orthogonal to every member of a *second* image
family `R'` whenever the two families are orthogonal (`D.imageFamily.Orthogonal R'`, the (5.2.e)
hypothesis).  `⟨X, α⟩ = ⟨∑_{β∈R(χ)} coeff β • β, α⟩ = ∑ coeff β · ⟨β, α⟩ = 0` since each `⟨β, α⟩ =
0`.  This is the per-character half of the (5.6.1) remark "`χᵢ^{τ₁}` is orthogonal to `R(χ)` by
(5.5) and (5.2.e)" (mmd L77): for the family member `χ' := χᵢ` (with `D` its `ψ = 0` decomposition,
so `χᵢ^{τ₁} = D.X` by (5.5)) and the distinguished `R' := R(χ)`. -/
theorem inner_X_orthogonal_imageSet_of_orthogonal
    {χ' : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    (R' : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ')
    (hortho : D.imageFamily.Orthogonal R')
    {α : ClassFunction G ℂ} (hα : α ∈ R'.imageSet) :
    ClassFunction.inner D.X α = 0 := by
  rw [D.X_eq, OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun β hβ => ?_
  rw [ClassFunction.inner_smul_left, hortho.inner_eq_zero hβ hα, mul_zero]

end CharacterPsiDecomposition

/-- Pointwise evaluation of a finite sum of class functions (the `Finset` analogue of
`ClassFunction.add_apply`). -/
theorem classFunction_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → ClassFunction L ℂ) (g : L) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]

namespace IntegralCharacterMap

open OddOrder.RepresentationTheory

variable [Fintype L] [Invertible (Nat.card L : ℂ)]

/-- The integral-linear functional `φ ↦ ⟨φ, η⟩` (linear in the **first** argument). -/
noncomputable def innerLeftℤ (η : ClassFunction L ℂ) : ClassFunction L ℂ →ₗ[ℤ] ℂ where
  toFun φ := ClassFunction.inner φ η
  map_add' a b := ClassFunction.inner_add_left a b η
  map_smul' n a := by
    simp only [RingHom.id_apply, zsmul_eq_mul]
    rw [← Int.cast_smul_eq_zsmul ℂ n a, ClassFunction.inner_smul_left]

@[simp] theorem innerLeftℤ_apply (η φ : ClassFunction L ℂ) :
    innerLeftℤ (L := L) η φ = ClassFunction.inner φ η := rfl

/-- The Gram–Schmidt residual `φ⊥ = φ − ⟨φ,χ⟩χ − ⟨φ,χ̄⟩χ̄` against `{χ, χ̄}`, as a `ℤ`-linear
endomorphism of `ClassFunction L ℂ`.  This is `ℂ`-linear (the inner product is `ℂ`-linear in
its first argument), and in particular `ℤ`-linear, so it composes with the `ℤ`-linear `τ₁`. -/
noncomputable def orthoResidualMap (χ chibar : ClassFunction L ℂ) :
    ClassFunction L ℂ →ₗ[ℤ] ClassFunction L ℂ :=
  LinearMap.id - (innerLeftℤ (L := L) χ).smulRight χ
    - (innerLeftℤ (L := L) chibar).smulRight chibar

@[simp] theorem orthoResidualMap_apply (χ chibar φ : ClassFunction L ℂ) :
    orthoResidualMap (L := L) χ chibar φ =
      φ - ClassFunction.inner φ χ • χ - ClassFunction.inner φ chibar • chibar := by
  simp [orthoResidualMap, LinearMap.smulRight_apply]

/-- The residual `φ⊥` is orthogonal to `χ` (using orthonormality of `{χ, χ̄}`). -/
theorem inner_orthoResidualMap_left {χ chibar : ClassFunction L ℂ}
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (φ : ClassFunction L ℂ) :
    ClassFunction.inner (orthoResidualMap (L := L) χ chibar φ) χ = 0 := by
  rw [orthoResidualMap_apply, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, hχχ, hχbarχ,
    mul_one, mul_zero, sub_zero, sub_self]

/-- The residual `φ⊥` is orthogonal to `χ̄` (using orthonormality of `{χ, χ̄}`). -/
theorem inner_orthoResidualMap_right {χ chibar : ClassFunction L ℂ}
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (φ : ClassFunction L ℂ) :
    ClassFunction.inner (orthoResidualMap (L := L) χ chibar φ) chibar = 0 := by
  rw [orthoResidualMap_apply, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, hχχbar, hχbarχbar,
    mul_one, mul_zero, sub_zero, sub_self]

/-- The rank-`2` **re-targeting** of an integral isometry `τ₁`:
`φ ↦ τ₁ φ⊥ + ⟨φ,χ⟩·X + ⟨φ,χ̄⟩·X̄`, where `φ⊥ = φ − ⟨φ,χ⟩χ − ⟨φ,χ̄⟩χ̄` is the Gram–Schmidt
residual.  For an orthonormal pair `{χ, χ̄}` this sends `χ ↦ X`, `χ̄ ↦ X̄`, and keeps `τ₁`
on the orthogonal complement `{χ, χ̄}^⊥` (where `φ⊥ = φ`).

Concretely, `τ₂ = τ₁ ∘ φ⊥ + ⟨·,χ⟩·X + ⟨·,χ̄⟩·X̄`, a genuine `ℤ`-linear map (the projection is
`ℂ`-linear, hence `ℤ`-linear; the inner-product functionals are `ℤ`-linear).  Note `τ₁` is *not*
applied to the complex Fourier coefficients, so the construction is correct even though `τ₁` is
only `ℤ`-linear. -/
noncomputable def retarget (τ₁ : IntegralCharacterMap L G)
    (χ chibar : ClassFunction L ℂ) (X Xbar : ClassFunction G ℂ) :
    IntegralCharacterMap L G :=
  τ₁ ∘ₗ orthoResidualMap (L := L) χ chibar
    + (innerLeftℤ (L := L) χ).smulRight X
    + (innerLeftℤ (L := L) chibar).smulRight Xbar

@[simp] theorem retarget_apply (τ₁ : IntegralCharacterMap L G)
    (χ chibar : ClassFunction L ℂ) (X Xbar : ClassFunction G ℂ) (φ : ClassFunction L ℂ) :
    retarget τ₁ χ chibar X Xbar φ =
      τ₁ (orthoResidualMap (L := L) χ chibar φ)
        + ClassFunction.inner φ χ • X + ClassFunction.inner φ chibar • Xbar := by
  simp [retarget, LinearMap.smulRight_apply]

variable {τ₁ : IntegralCharacterMap L G} {χ chibar : ClassFunction L ℂ}
  {X Xbar : ClassFunction G ℂ}

/-- On the orthogonal complement of `{χ, χ̄}` the re-targeting agrees with `τ₁`. -/
theorem retarget_eq_of_orthogonal {φ : ClassFunction L ℂ}
    (hφχ : ClassFunction.inner φ χ = 0) (hφχbar : ClassFunction.inner φ chibar = 0) :
    retarget τ₁ χ chibar X Xbar φ = τ₁ φ := by
  rw [retarget_apply, hφχ, hφχbar, zero_smul, zero_smul, add_zero, add_zero,
    orthoResidualMap_apply, hφχ, hφχbar, zero_smul, zero_smul, sub_zero, sub_zero]

/-- `χ ↦ X` for an orthonormal pair `{χ, χ̄}`. -/
theorem retarget_apply_left
    (hχχ : ClassFunction.inner χ χ = 1) (hχχbar : ClassFunction.inner χ chibar = 0) :
    retarget τ₁ χ chibar X Xbar χ = X := by
  have hres : orthoResidualMap (L := L) χ chibar χ = 0 := by
    rw [orthoResidualMap_apply, hχχ, hχχbar, one_smul, zero_smul, sub_zero, sub_self]
  rw [retarget_apply, hres, map_zero, hχχ, hχχbar, one_smul, zero_smul, add_zero, zero_add]

/-- `χ̄ ↦ X̄` for an orthonormal pair `{χ, χ̄}`. -/
theorem retarget_apply_right
    (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hχbarχbar : ClassFunction.inner chibar chibar = 1) :
    retarget τ₁ χ chibar X Xbar chibar = Xbar := by
  have hres : orthoResidualMap (L := L) χ chibar chibar = 0 := by
    rw [orthoResidualMap_apply, hχbarχ, hχbarχbar, one_smul, zero_smul, sub_zero, sub_self]
  rw [retarget_apply, hres, map_zero, hχbarχ, hχbarχbar, one_smul, zero_smul, add_zero, zero_add]

/-- **Block expansion of a sesquilinear inner product against an orthonormal pair.**
For `u, u' ∈ W` with `⟨e,e⟩ = ⟨f,f⟩ = 1`, `⟨e,f⟩ = ⟨f,e⟩ = 0`, and `u, u'` each orthogonal
to `e` and `f`, the inner product of `u + s·e + t·f` and `u' + s'·e + t'·f` collapses to
`⟨u,u'⟩ + s·conj s' + t·conj t'`.  This is the common normal form both sides of the
re-targeting isometry reduce to. -/
theorem inner_block_expand {W : Type*} [Group W] [Fintype W] [Invertible (Nat.card W : ℂ)]
    {e f u u' : ClassFunction W ℂ} {s t s' t' : ℂ}
    (hee : ClassFunction.inner e e = 1) (hff : ClassFunction.inner f f = 1)
    (hef : ClassFunction.inner e f = 0) (hfe : ClassFunction.inner f e = 0)
    (hue : ClassFunction.inner u e = 0) (huf : ClassFunction.inner u f = 0)
    (hu'e : ClassFunction.inner u' e = 0) (hu'f : ClassFunction.inner u' f = 0) :
    ClassFunction.inner (u + s • e + t • f) (u' + s' • e + t' • f) =
      ClassFunction.inner u u' + s * star s' + t * star t' := by
  have heu' : ClassFunction.inner e u' = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hu'e, star_zero]
  have hfu' : ClassFunction.inner f u' = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hu'f, star_zero]
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    hue, huf, heu', hfu', hee, hff, hef, hfe]
  ring

/-- The Gram–Schmidt residual against an orthonormal pair `{χ, χ̄}` carries
`ℤ[S₁ ∪ {χ, χ̄}]` into `ℤ[S₁]`, provided `χ, χ̄ ⊥ S₁`.

For a generator `x ∈ S₁` the residual is `x` itself (`x ⊥ {χ, χ̄}`); for `x = χ`
(resp. `χ̄`) it is `0`; and `orthoResidualMap` is `ℤ`-linear, so the property
propagates over the `ℤ`-span by `span_induction`.  This is the lattice fact making
the re-targeting an isometry on the *integral* span `ℤ[S₁ ∪ {χ, χ̄}]` using only
the coherence isometry of `τ₁` on `ℤ[S₁]`. -/
theorem orthoResidualMap_mem_zSpan {χ chibar : ClassFunction L ℂ}
    {S₁ : Set (ClassFunction L ℂ)}
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ (S₁ ∪ {χ, chibar})) :
    orthoResidualMap (L := L) χ chibar φ ∈ Submodule.span ℤ S₁ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      rcases hx with hxS1 | hxpair
      · -- `x ∈ S₁`: residual is `x ∈ ℤ[S₁]` since `x ⊥ {χ, χ̄}`.
        have hxχ : ClassFunction.inner x χ = 0 := by
          rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 x hxS1, star_zero]
        have hxχbar : ClassFunction.inner x chibar = 0 := by
          rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 x hxS1, star_zero]
        rw [orthoResidualMap_apply, hxχ, hxχbar, zero_smul, zero_smul, sub_zero, sub_zero]
        exact Submodule.subset_span hxS1
      · rcases hxpair with rfl | rfl
        · -- `x = χ`: residual is `0`.
          rw [orthoResidualMap_apply, hχχ, hχχbar, one_smul, zero_smul, sub_zero, sub_self]
          exact Submodule.zero_mem _
        · -- `x = χ̄`: residual is `0`.
          rw [orthoResidualMap_apply, hχbarχ, hχbarχbar, one_smul, zero_smul, sub_zero,
            sub_self]
          exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ a ih

/-- **The integral-span re-targeting isometry (the genuine (5.6.3) lattice isometry).**

The honestly-satisfiable companion of `retarget_inner_eq_on`, stated over the *integral*
span `ℤ[S₁ ∪ {χ, χ̄}]` instead of a complex submodule.  Re-targeting an isometry `τ₁` (here only
required isometric on `ℤ[S₁]` — exactly the coherence isometry of `S₁`) preserves `⟨·,·⟩` on all of
`ℤ[S₁ ∪ {χ, χ̄}]`, given:

* `{χ, χ̄}` orthonormal with `χ, χ̄ ⊥ S₁`, and the target pair `{X, X̄}` orthonormal in `ℤ[Irr G]`;
* the honest `(5.5)+(5.2.e)` orthogonality `X, X̄ ⊥ τ₁ ξ` for **`ξ ∈ ℤ[S₁]`** (not the over-strong
  global version, and not posited beyond the lattice `S₁^{τ₁}`).

Every Gram–Schmidt residual of `φ ∈ ℤ[S₁ ∪ {χ, χ̄}]` lands in `ℤ[S₁]`
(`orthoResidualMap_mem_zSpan`), so the block expansion `inner_block_expand` closes the proof using
only the `ℤ[S₁]`-isometry of `τ₁` and the lattice orthogonality.  This is what realizes the weakened
`IsCoherent.extension_inner_eq` for the union `S₁ ∪ {χ, χ̄}`. -/
theorem retarget_inner_eq_on_zSpan_union [Fintype G] [Invertible (Nat.card G : ℂ)]
    {τ₁ : IntegralCharacterMap L G} {χ chibar : ClassFunction L ℂ}
    {X Xbar : ClassFunction G ℂ} {S₁ : Set (ClassFunction L ℂ)}
    (hτ₁ : ∀ u v : ClassFunction L ℂ, u ∈ Submodule.span ℤ S₁ → v ∈ Submodule.span ℤ S₁ →
      ClassFunction.inner (τ₁ u) (τ₁ v) = ClassFunction.inner u v)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hXX : ClassFunction.inner X X = 1) (hXbarXbar : ClassFunction.inner Xbar Xbar = 1)
    (hXXbar : ClassFunction.inner X Xbar = 0) (hXbarX : ClassFunction.inner Xbar X = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (τ₁ ξ) X = 0)
    (hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (τ₁ ξ) Xbar = 0)
    {φ ψ : ClassFunction L ℂ}
    (hφ : φ ∈ Submodule.span ℤ (S₁ ∪ {χ, chibar}))
    (hψ : ψ ∈ Submodule.span ℤ (S₁ ∪ {χ, chibar})) :
    ClassFunction.inner (retarget τ₁ χ chibar X Xbar φ) (retarget τ₁ χ chibar X Xbar ψ) =
      ClassFunction.inner φ ψ := by
  set s := ClassFunction.inner φ χ with hs
  set t := ClassFunction.inner φ chibar with ht
  set s' := ClassFunction.inner ψ χ with hs'
  set t' := ClassFunction.inner ψ chibar with ht'
  set φperp := orthoResidualMap (L := L) χ chibar φ with hφperp
  set ψperp := orthoResidualMap (L := L) χ chibar ψ with hψperp
  -- The residuals lie in `ℤ[S₁]`.
  have hφperpS1 : φperp ∈ Submodule.span ℤ S₁ :=
    orthoResidualMap_mem_zSpan hχχ hχbarχbar hχχbar hχbarχ hχ_S1 hχbar_S1 hφ
  have hψperpS1 : ψperp ∈ Submodule.span ℤ S₁ :=
    orthoResidualMap_mem_zSpan hχχ hχbarχbar hχχbar hχbarχ hχ_S1 hχbar_S1 hψ
  -- Orthogonality of the residuals to `{χ, χ̄}`.
  have hφperp_χ : ClassFunction.inner φperp χ = 0 :=
    inner_orthoResidualMap_left hχχ hχbarχ φ
  have hφperp_χbar : ClassFunction.inner φperp chibar = 0 :=
    inner_orthoResidualMap_right hχχbar hχbarχbar φ
  have hψperp_χ : ClassFunction.inner ψperp χ = 0 :=
    inner_orthoResidualMap_left hχχ hχbarχ ψ
  have hψperp_χbar : ClassFunction.inner ψperp chibar = 0 :=
    inner_orthoResidualMap_right hχχbar hχbarχbar ψ
  -- Image side.
  have himg : ClassFunction.inner (retarget τ₁ χ chibar X Xbar φ)
      (retarget τ₁ χ chibar X Xbar ψ) =
      ClassFunction.inner (τ₁ φperp) (τ₁ ψperp) + s * star s' + t * star t' := by
    rw [retarget_apply, retarget_apply, ← hφperp, ← hψperp, ← hs, ← ht, ← hs', ← ht']
    exact inner_block_expand hXX hXbarXbar hXXbar hXbarX
      (hX_ortho φperp hφperpS1) (hXbar_ortho φperp hφperpS1)
      (hX_ortho ψperp hψperpS1) (hXbar_ortho ψperp hψperpS1)
  -- Source side.
  have hsrc : ClassFunction.inner φ ψ =
      ClassFunction.inner φperp ψperp + s * star s' + t * star t' := by
    have hφ' : φ = φperp + s • χ + t • chibar := by
      rw [hφperp, orthoResidualMap_apply, ← hs, ← ht]; abel
    have hψ' : ψ = ψperp + s' • χ + t' • chibar := by
      rw [hψperp, orthoResidualMap_apply, ← hs', ← ht']; abel
    rw [hφ', hψ']
    exact inner_block_expand hχχ hχbarχbar hχχbar hχbarχ
      hφperp_χ hφperp_χbar hψperp_χ hψperp_χbar
  rw [himg, hsrc, hτ₁ φperp ψperp hφperpS1 hψperpS1]

omit [Fintype L] [Invertible (Nat.card L : ℂ)] in
/-- **Two integral character maps agreeing on a set agree on its integral span.**
If `f, g : IntegralCharacterMap L G` agree on every element of `T ⊆ ClassFunction L ℂ`, they
agree on all of `Submodule.span ℤ T`.  Pure `span_induction`; reused to discharge
`extends_on_supported`. -/
theorem eq_on_zSpan_of_eq_on {f g : IntegralCharacterMap L G}
    {T : Set (ClassFunction L ℂ)} (h : ∀ x ∈ T, f x = g x)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ T) :
    f φ = g φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ ihx ihy => rw [map_add, map_add, ihx, ihy]
  | smul a x _ ih => rw [map_zsmul, map_zsmul, ih]

/-- A class function orthogonal to every element of `T` is orthogonal to all of `ℤ[T]`. -/
theorem inner_eq_zero_of_mem_zSpan {η : ClassFunction L ℂ}
    {T : Set (ClassFunction L ℂ)} (h : ∀ x ∈ T, ClassFunction.inner η x = 0)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ T) :
    ClassFunction.inner η φ = 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ClassFunction.inner_zero_right η
  | add x y _ _ ihx ihy => rw [ClassFunction.inner_add_right, ihx, ihy, add_zero]
  | smul a x _ ih =>
      rw [← Int.cast_smul_eq_zsmul ℂ a x,
        OddOrder.RepresentationTheory.inner_smul_right, ih, mul_zero]

noncomputable def coherentImageMap {n : ℕ} (χ : Fin n → ClassFunction L ℂ)
    (X : Fin n → ClassFunction G ℂ) : IntegralCharacterMap L G :=
  ∑ j : Fin n, (innerLeftℤ (L := L) (χ j)).smulRight (X j)

@[simp] theorem coherentImageMap_apply {n : ℕ} (χ : Fin n → ClassFunction L ℂ)
    (X : Fin n → ClassFunction G ℂ) (φ : ClassFunction L ℂ) :
    coherentImageMap (L := L) (G := G) χ X φ =
      ∑ j : Fin n, ClassFunction.inner φ (χ j) • X j := by
  simp only [coherentImageMap, LinearMap.sum_apply, LinearMap.smulRight_apply, innerLeftℤ_apply]

/-- `ν χₖ = Xₖ` for an orthonormal source family. -/
theorem coherentImageMap_apply_eq {n : ℕ} {χ : Fin n → ClassFunction L ℂ}
    {X : Fin n → ClassFunction G ℂ}
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    (k : Fin n) :
    coherentImageMap (L := L) (G := G) χ X (χ k) = X k := by
  classical
  rw [coherentImageMap_apply, Finset.sum_eq_single k]
  · rw [horthχ k k, if_pos rfl, one_smul]
  · intro j _ hjk; rw [horthχ k j, if_neg (fun h => hjk h.symm), zero_smul]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- **The two-family Fourier glue** `ν = νX-image on `range χX` ⊕ νY-image on `range χY``.
For orthonormal families `χX`, `χY` with mutually orthogonal ranges, `ν φ =
∑ᵢ ⟨φ,χXᵢ⟩•νX(χXᵢ) + ∑ⱼ ⟨φ,χYⱼ⟩•νY(χYⱼ)` sends `χXₖ ↦ νX(χXₖ)` and `χYₖ ↦ νY(χYₖ)` — the cross
terms vanish by `⟨χXₖ,χYⱼ⟩ = 0`.  This is the `τ₃` glue of Peterfalvi (6.8.1): with `νX = τ₂`
(the `X`-coherence extension) and `νY = τ₁` (the `Y`-coherence extension), it is the combined map
agreeing with `τ₂` on `X` and `τ₁` on `Y`, ready for `coherentUnion_of_glued` (the only remaining
input being `himg_ortho`). -/
noncomputable def coherentImageMapGlue {n m : ℕ} (χX : Fin n → ClassFunction L ℂ)
    (χY : Fin m → ClassFunction L ℂ) (νX νY : IntegralCharacterMap L G) :
    IntegralCharacterMap L G :=
  coherentImageMap (L := L) (G := G) χX (fun i => νX (χX i))
    + coherentImageMap (L := L) (G := G) χY (fun j => νY (χY j))

/-- The glue sends `χXₖ ↦ νX(χXₖ)`: the `νX`-image term is Parseval-exact (`χX` orthonormal), the
`νY`-image term vanishes (`χXₖ ⊥ χYⱼ`). -/
theorem coherentImageMapGlue_apply_left {n m : ℕ} {χX : Fin n → ClassFunction L ℂ}
    {χY : Fin m → ClassFunction L ℂ} {νX νY : IntegralCharacterMap L G}
    (horthX : ∀ i j, ClassFunction.inner (χX i) (χX j) = if i = j then (1 : ℂ) else 0)
    (hXY : ∀ (k : Fin n) (j : Fin m), ClassFunction.inner (χX k) (χY j) = 0) (k : Fin n) :
    coherentImageMapGlue (L := L) (G := G) χX χY νX νY (χX k) = νX (χX k) := by
  rw [coherentImageMapGlue, LinearMap.add_apply, coherentImageMap_apply_eq horthX k,
    coherentImageMap_apply, Finset.sum_eq_zero (fun j _ => by rw [hXY k j, zero_smul]), add_zero]

/-- The glue sends `χYₖ ↦ νY(χYₖ)` (symmetric to `coherentImageMapGlue_apply_left`). -/
theorem coherentImageMapGlue_apply_right {n m : ℕ} {χX : Fin n → ClassFunction L ℂ}
    {χY : Fin m → ClassFunction L ℂ} {νX νY : IntegralCharacterMap L G}
    (horthY : ∀ i j, ClassFunction.inner (χY i) (χY j) = if i = j then (1 : ℂ) else 0)
    (hXY : ∀ (i : Fin n) (k : Fin m), ClassFunction.inner (χY k) (χX i) = 0) (k : Fin m) :
    coherentImageMapGlue (L := L) (G := G) χX χY νX νY (χY k) = νY (χY k) := by
  rw [coherentImageMapGlue, LinearMap.add_apply, coherentImageMap_apply,
    Finset.sum_eq_zero (fun i _ => by rw [hXY i k, zero_smul]), zero_add,
    coherentImageMap_apply_eq horthY k]

open scoped Classical in
/-- **Existence of the two-family glue over orthonormal sets** (Peterfalvi (6.8.1) `τ₃`, set form).
For finite, mutually orthogonal orthonormal sets `X`, `Y ⊆ CF(L)` and integral maps `νX`, `νY`,
there is an `IntegralCharacterMap ν` agreeing with `νX` on `X` and `νY` on `Y` — namely
`coherentImageMapGlue` of any enumerations (agreement `coherentImageMapGlue_apply_left/right`).
With `νX = τ₂` (`X`-coherence extension) and `νY = τ₁` (`Y`-coherence extension) this supplies the
`ν` that `coherentUnion_of_glued` takes, reducing the (6.8) `X ∪ Y`-coherence to `himg_ortho`. -/
theorem exists_integralCharacterMap_glue_of_orthonormal
    {X Y : Set (ClassFunction L ℂ)} (hXfin : X.Finite) (hYfin : Y.Finite)
    (hXorth : ∀ x ∈ X, ∀ x' ∈ X, ClassFunction.inner x x' = if x = x' then (1 : ℂ) else 0)
    (hYorth : ∀ y ∈ Y, ∀ y' ∈ Y, ClassFunction.inner y y' = if y = y' then (1 : ℂ) else 0)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ClassFunction.inner x y = 0)
    (νX νY : IntegralCharacterMap L G) :
    ∃ ν : IntegralCharacterMap L G, (∀ x ∈ X, ν x = νX x) ∧ (∀ y ∈ Y, ν y = νY y) := by
  classical
  let χX : Fin hXfin.toFinset.card → ClassFunction L ℂ :=
    fun i => ↑(hXfin.toFinset.equivFin.symm i)
  let χY : Fin hYfin.toFinset.card → ClassFunction L ℂ :=
    fun j => ↑(hYfin.toFinset.equivFin.symm j)
  have hχX_mem : ∀ i, χX i ∈ X := fun i =>
    hXfin.mem_toFinset.mp (hXfin.toFinset.equivFin.symm i).2
  have hχY_mem : ∀ j, χY j ∈ Y := fun j =>
    hYfin.mem_toFinset.mp (hYfin.toFinset.equivFin.symm j).2
  have horthX : ∀ i j, ClassFunction.inner (χX i) (χX j) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [hXorth (χX i) (hχX_mem i) (χX j) (hχX_mem j)]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · refine (if_neg ?_).trans (if_neg hij).symm
      exact fun hx => hij (hXfin.toFinset.equivFin.symm.injective (Subtype.ext hx))
  have horthY : ∀ i j, ClassFunction.inner (χY i) (χY j) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [hYorth (χY i) (hχY_mem i) (χY j) (hχY_mem j)]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · refine (if_neg ?_).trans (if_neg hij).symm
      exact fun hy => hij (hYfin.toFinset.equivFin.symm.injective (Subtype.ext hy))
  have hXYfam : ∀ (i : Fin hXfin.toFinset.card) (j : Fin hYfin.toFinset.card),
      ClassFunction.inner (χX i) (χY j) = 0 :=
    fun i j => hXY (χX i) (hχX_mem i) (χY j) (hχY_mem j)
  have hYXfam : ∀ (i : Fin hXfin.toFinset.card) (j : Fin hYfin.toFinset.card),
      ClassFunction.inner (χY j) (χX i) = 0 := fun i j => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXYfam i j, star_zero]
  refine ⟨coherentImageMapGlue χX χY νX νY, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ : ∃ i, χX i = x :=
      ⟨hXfin.toFinset.equivFin ⟨x, hXfin.mem_toFinset.mpr hx⟩, by simp [χX]⟩
    exact coherentImageMapGlue_apply_left horthX hXYfam i
  · intro y hy
    obtain ⟨j, rfl⟩ : ∃ j, χY j = y :=
      ⟨hYfin.toFinset.equivFin ⟨y, hYfin.mem_toFinset.mpr hy⟩, by simp [χY]⟩
    exact coherentImageMapGlue_apply_right horthY hYXfam j

/-- **Orthogonal (non-normalized) Fourier reconstruction** sends `χₖ ↦ Xₖ`.  For a *pairwise-
orthogonal* family `χ` (distinct members orthogonal, each of nonzero norm — **not** required
orthonormal), the norm-rescaled map `φ ↦ ∑ⱼ ⟨φ, χⱼ⟩ • (⟨χⱼ,χⱼ⟩⁻¹ • Xⱼ)` sends `χₖ ↦ Xₖ`: the cross
terms vanish by orthogonality and the diagonal term is `⟨χₖ,χₖ⟩ • ⟨χₖ,χₖ⟩⁻¹ • Xₖ = Xₖ` (norm
nonzero).  This is the `orthonormal → orthogonal` generalization of `coherentImageMap_apply_eq`
(there `⟨χⱼ,χⱼ⟩ = 1` makes the rescaling trivial). -/
theorem coherentImageMap_apply_eq_of_orthogonal {n : ℕ} {χ : Fin n → ClassFunction L ℂ}
    {X : Fin n → ClassFunction G ℂ}
    (horthχ : ∀ i j, i ≠ j → ClassFunction.inner (χ i) (χ j) = 0)
    (hnorm : ∀ j, ClassFunction.inner (χ j) (χ j) ≠ 0) (k : Fin n) :
    coherentImageMap (L := L) (G := G) χ
        (fun j => (ClassFunction.inner (χ j) (χ j))⁻¹ • X j) (χ k) = X k := by
  classical
  simp only [coherentImageMap_apply]
  rw [Finset.sum_eq_single k]
  · rw [smul_smul, mul_inv_cancel₀ (hnorm k), one_smul]
  · intro j _ hjk
    rw [horthχ k j fun h => hjk h.symm, zero_smul]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- **Two-family orthogonal glue** — the `τ₃` of Peterfalvi (6.8.1) for *non-normalized* families.
`ν = [norm-rescaled reconstruction of νX over χX] + [norm-rescaled reconstruction of νY over χY]`.
For pairwise-orthogonal `χX`, `χY` (each of nonzero norm) with mutually orthogonal ranges it sends
`χXₖ ↦ νX(χXₖ)` and `χYₖ ↦ νY(χYₖ)`; the cross terms vanish by `⟨χXₖ,χYⱼ⟩ = 0`.  Unlike
`coherentImageMapGlue` this does **not** require the families orthonormal. -/
noncomputable def coherentImageMapGlueOrthogonal {n m : ℕ} (χX : Fin n → ClassFunction L ℂ)
    (χY : Fin m → ClassFunction L ℂ) (νX νY : IntegralCharacterMap L G) :
    IntegralCharacterMap L G :=
  coherentImageMap (L := L) (G := G) χX
      (fun i => (ClassFunction.inner (χX i) (χX i))⁻¹ • νX (χX i))
    + coherentImageMap (L := L) (G := G) χY
      (fun j => (ClassFunction.inner (χY j) (χY j))⁻¹ • νY (χY j))

/-- The orthogonal glue sends `χXₖ ↦ νX(χXₖ)`: the `νX`-reconstruction is exact for the orthogonal
family `χX` (`coherentImageMap_apply_eq_of_orthogonal`), the `νY`-reconstruction vanishes
(`χXₖ ⊥ χYⱼ`). -/
theorem coherentImageMapGlueOrthogonal_apply_left {n m : ℕ} {χX : Fin n → ClassFunction L ℂ}
    {χY : Fin m → ClassFunction L ℂ} {νX νY : IntegralCharacterMap L G}
    (horthX : ∀ i j, i ≠ j → ClassFunction.inner (χX i) (χX j) = 0)
    (hnormX : ∀ i, ClassFunction.inner (χX i) (χX i) ≠ 0)
    (hXY : ∀ (k : Fin n) (j : Fin m), ClassFunction.inner (χX k) (χY j) = 0) (k : Fin n) :
    coherentImageMapGlueOrthogonal (L := L) (G := G) χX χY νX νY (χX k) = νX (χX k) := by
  rw [coherentImageMapGlueOrthogonal, LinearMap.add_apply,
    coherentImageMap_apply_eq_of_orthogonal horthX hnormX k]
  simp only [coherentImageMap_apply]
  rw [Finset.sum_eq_zero fun j _ => by rw [hXY k j, zero_smul], add_zero]

/-- The orthogonal glue sends `χYₖ ↦ νY(χYₖ)` (symmetric to
`coherentImageMapGlueOrthogonal_apply_left`). -/
theorem coherentImageMapGlueOrthogonal_apply_right {n m : ℕ} {χX : Fin n → ClassFunction L ℂ}
    {χY : Fin m → ClassFunction L ℂ} {νX νY : IntegralCharacterMap L G}
    (horthY : ∀ i j, i ≠ j → ClassFunction.inner (χY i) (χY j) = 0)
    (hnormY : ∀ i, ClassFunction.inner (χY i) (χY i) ≠ 0)
    (hYX : ∀ (i : Fin n) (k : Fin m), ClassFunction.inner (χY k) (χX i) = 0) (k : Fin m) :
    coherentImageMapGlueOrthogonal (L := L) (G := G) χX χY νX νY (χY k) = νY (χY k) := by
  rw [coherentImageMapGlueOrthogonal, LinearMap.add_apply,
    coherentImageMap_apply_eq_of_orthogonal horthY hnormY k]
  simp only [coherentImageMap_apply]
  rw [Finset.sum_eq_zero fun i _ => by rw [hYX i k, zero_smul], zero_add]

open scoped Classical in
/-- **Existence of the two-family glue over pairwise-orthogonal (non-normalized) sets**
(Peterfalvi (6.8.1) `τ₃`, the form (11.8.6) needs).  For finite, mutually orthogonal sets `X`,
`Y ⊆ CF(L)` that are each *pairwise orthogonal* with members of nonzero norm (**not** required
orthonormal — Peterfalvi's `S₂ = 𝒮(C) − 𝒮(HC)` is a family of reducible induced characters), and
integral maps `νX`, `νY`, there is an `IntegralCharacterMap ν` agreeing with `νX` on `X` and `νY`
on `Y`.  This is the `ν` (`hagreeX`/`hagreeY`) that `coherentUnion_of_glued*` takes; it strengthens
`exists_integralCharacterMap_glue_of_orthonormal` by dropping the orthonormality of both families
(the diagonal normalization `⟨·,·⟩⁻¹` in `coherentImageMapGlueOrthogonal` absorbs the non-unit
norms).  Mirrors mathcomp `bridge_coherent`'s `Zisometry_of_cfnorm` extension over the merely
`pairwise_orthogonal` source and image sequences. -/
theorem exists_integralCharacterMap_glue_of_orthogonal
    {X Y : Set (ClassFunction L ℂ)} (hXfin : X.Finite) (hYfin : Y.Finite)
    (hXorth : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → ClassFunction.inner x x' = 0)
    (hXnorm : ∀ x ∈ X, ClassFunction.inner x x ≠ 0)
    (hYorth : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ClassFunction.inner y y' = 0)
    (hYnorm : ∀ y ∈ Y, ClassFunction.inner y y ≠ 0)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ClassFunction.inner x y = 0)
    (νX νY : IntegralCharacterMap L G) :
    ∃ ν : IntegralCharacterMap L G, (∀ x ∈ X, ν x = νX x) ∧ (∀ y ∈ Y, ν y = νY y) := by
  classical
  let χX : Fin hXfin.toFinset.card → ClassFunction L ℂ :=
    fun i => ↑(hXfin.toFinset.equivFin.symm i)
  let χY : Fin hYfin.toFinset.card → ClassFunction L ℂ :=
    fun j => ↑(hYfin.toFinset.equivFin.symm j)
  have hχX_mem : ∀ i, χX i ∈ X := fun i =>
    hXfin.mem_toFinset.mp (hXfin.toFinset.equivFin.symm i).2
  have hχY_mem : ∀ j, χY j ∈ Y := fun j =>
    hYfin.mem_toFinset.mp (hYfin.toFinset.equivFin.symm j).2
  have horthX : ∀ i j, i ≠ j → ClassFunction.inner (χX i) (χX j) = 0 := fun i j hij =>
    hXorth (χX i) (hχX_mem i) (χX j) (hχX_mem j)
      (fun hx => hij (hXfin.toFinset.equivFin.symm.injective (Subtype.ext hx)))
  have horthY : ∀ i j, i ≠ j → ClassFunction.inner (χY i) (χY j) = 0 := fun i j hij =>
    hYorth (χY i) (hχY_mem i) (χY j) (hχY_mem j)
      (fun hy => hij (hYfin.toFinset.equivFin.symm.injective (Subtype.ext hy)))
  have hnormX : ∀ i, ClassFunction.inner (χX i) (χX i) ≠ 0 := fun i => hXnorm (χX i) (hχX_mem i)
  have hnormY : ∀ j, ClassFunction.inner (χY j) (χY j) ≠ 0 := fun j => hYnorm (χY j) (hχY_mem j)
  have hXYfam : ∀ (k : Fin hXfin.toFinset.card) (j : Fin hYfin.toFinset.card),
      ClassFunction.inner (χX k) (χY j) = 0 :=
    fun k j => hXY (χX k) (hχX_mem k) (χY j) (hχY_mem j)
  have hYXfam : ∀ (i : Fin hXfin.toFinset.card) (k : Fin hYfin.toFinset.card),
      ClassFunction.inner (χY k) (χX i) = 0 := fun i k => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXYfam i k, star_zero]
  refine ⟨coherentImageMapGlueOrthogonal χX χY νX νY, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ : ∃ i, χX i = x :=
      ⟨hXfin.toFinset.equivFin ⟨x, hXfin.mem_toFinset.mpr hx⟩, by simp [χX]⟩
    exact coherentImageMapGlueOrthogonal_apply_left horthX hnormX hXYfam i
  · intro y hy
    obtain ⟨j, rfl⟩ : ∃ j, χY j = y :=
      ⟨hYfin.toFinset.equivFin ⟨y, hYfin.mem_toFinset.mpr hy⟩, by simp [χY]⟩
    exact coherentImageMapGlueOrthogonal_apply_right horthY hnormY hYXfam j

/-- **Fourier expansion on the integral span of an orthonormal family.**
Every `φ ∈ ℤ[range χ]` equals `∑ⱼ ⟨φ, χⱼ⟩ • χⱼ`. -/
theorem eq_sum_inner_smul_of_mem_span {n : ℕ} {χ : Fin n → ClassFunction L ℂ}
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ (Set.range χ)) :
    ∑ j : Fin n, ClassFunction.inner φ (χ j) • χ j = φ := by
  classical
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [Finset.sum_eq_single k]
      · rw [horthχ k k, if_pos rfl, one_smul]
      · intro j _ hjk; rw [horthχ k j, if_neg (fun h => hjk h.symm), zero_smul]
      · intro h; exact absurd (Finset.mem_univ k) h
  | zero => simp
  | add x y _ _ ihx ihy =>
      simp only [ClassFunction.inner_add_left, add_smul]
      rw [Finset.sum_add_distrib, ihx, ihy]
  | smul a x _ ih =>
      have hcast : ∀ j, ClassFunction.inner (a • x) (χ j) • χ j
          = (a : ℂ) • (ClassFunction.inner x (χ j) • χ j) := fun j => by
        rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, mul_smul]
      simp only [hcast]
      rw [← Finset.smul_sum, ih, Int.cast_smul_eq_zsmul]

/-- **Parseval on the span:** for `φ ∈ ℤ[range χ]` and any `ψ`,
`⟨φ, ψ⟩ = ∑ⱼ ⟨φ, χⱼ⟩ · conj ⟨ψ, χⱼ⟩`. -/
theorem inner_eq_sum_inner_mul_conj {n : ℕ} {χ : Fin n → ClassFunction L ℂ}
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    {φ ψ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ (Set.range χ)) :
    ClassFunction.inner φ ψ =
      ∑ j : Fin n, ClassFunction.inner φ (χ j) * star (ClassFunction.inner ψ (χ j)) := by
  conv_lhs => rw [← eq_sum_inner_smul_of_mem_span horthχ hφ]
  rw [inner_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ClassFunction.inner_smul_left, inner_conj_symm ψ (χ j)]

/-- **The Fourier-image map is an isometry on the lattice `ℤ[range χ]`** when both `χ` and `X` are
orthonormal.  This is the lattice-relative `IsCoherent.extension_inner_eq` for an equal-degree set:
the `τ`-residual is inert on `ℤ[range χ]`, leaving pure Parseval. -/
theorem coherentImageMap_inner_eq [Fintype G] [Invertible (Nat.card G : ℂ)]
    {n : ℕ} {χ : Fin n → ClassFunction L ℂ} {X : Fin n → ClassFunction G ℂ}
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    (horthX : ∀ i j, ClassFunction.inner (X i) (X j) = if i = j then (1 : ℂ) else 0)
    {φ ψ : ClassFunction L ℂ}
    (hφ : φ ∈ Submodule.span ℤ (Set.range χ)) (_hψ : ψ ∈ Submodule.span ℤ (Set.range χ)) :
    ClassFunction.inner (coherentImageMap (L := L) (G := G) χ X φ)
        (coherentImageMap (L := L) (G := G) χ X ψ) =
      ClassFunction.inner φ ψ := by
  classical
  rw [inner_eq_sum_inner_mul_conj horthχ hφ, coherentImageMap_apply, coherentImageMap_apply,
    inner_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ClassFunction.inner_smul_left, inner_sum_right]
  congr 1
  rw [Finset.sum_eq_single j]
  · rw [OddOrder.RepresentationTheory.inner_smul_right, horthX j j, if_pos rfl, mul_one]
  · intro k _ hkj
    rw [OddOrder.RepresentationTheory.inner_smul_right, horthX j k,
      if_neg (fun h => hkj h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Weighted Fourier reconstruction**: for a pairwise-orthogonal family of nonzero norm,
`φ = ∑ⱼ (⟨φ, χⱼ⟩ / ⟨χⱼ, χⱼ⟩) • χⱼ` on `ℤ[range χ]`. -/
theorem eq_sum_inner_div_norm_smul_of_mem_span {n : ℕ} {χ : Fin n → ClassFunction L ℂ}
    (horthχ : ∀ i j, i ≠ j → ClassFunction.inner (χ i) (χ j) = 0)
    (hnorm : ∀ j, ClassFunction.inner (χ j) (χ j) ≠ 0)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ (Set.range χ)) :
    ∑ j : Fin n, ((ClassFunction.inner φ (χ j)) / ClassFunction.inner (χ j) (χ j)) • χ j = φ := by
  classical
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [Finset.sum_eq_single k]
      · rw [div_self (hnorm k), one_smul]
      · intro j _ hjk
        rw [horthχ k j fun h => hjk h.symm, zero_div, zero_smul]
      · intro h; exact absurd (Finset.mem_univ k) h
  | zero => simp
  | add x y _ _ ihx ihy =>
      simp only [ClassFunction.inner_add_left, add_div, add_smul]
      rw [Finset.sum_add_distrib, ihx, ihy]
  | smul a x _ ih =>
      have hcast : ∀ j, ((ClassFunction.inner (a • x) (χ j)) /
            ClassFunction.inner (χ j) (χ j)) • χ j
          = (a : ℂ) • ((ClassFunction.inner x (χ j) / ClassFunction.inner (χ j) (χ j)) • χ j) :=
        fun j => by
          rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, mul_div_assoc,
            mul_smul]
      simp only [hcast]
      rw [← Finset.smul_sum, ih, Int.cast_smul_eq_zsmul]

/-- **Weighted Parseval**: `⟨φ, ψ⟩ = ∑ⱼ ⟨φ, χⱼ⟩ · conj⟨ψ, χⱼ⟩ / ⟨χⱼ, χⱼ⟩` on `ℤ[range χ]`, for a
pairwise-orthogonal family of nonzero norm.  (`⟨χⱼ, χⱼ⟩` is real, so it is its own conjugate and
the single division is unambiguous.) -/
theorem inner_eq_sum_inner_mul_conj_div_norm {n : ℕ} {χ : Fin n → ClassFunction L ℂ}
    (horthχ : ∀ i j, i ≠ j → ClassFunction.inner (χ i) (χ j) = 0)
    (hnorm : ∀ j, ClassFunction.inner (χ j) (χ j) ≠ 0)
    {φ ψ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ (Set.range χ)) :
    ClassFunction.inner φ ψ =
      ∑ j : Fin n, ClassFunction.inner φ (χ j) * star (ClassFunction.inner ψ (χ j)) /
        ClassFunction.inner (χ j) (χ j) := by
  conv_lhs => rw [← eq_sum_inner_div_norm_smul_of_mem_span horthχ hnorm hφ]
  rw [inner_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ClassFunction.inner_smul_left, inner_conj_symm ψ (χ j), div_mul_eq_mul_div]

/-- **The weighted Fourier-image map is an isometry on `ℤ[range χ]`.**

For a pairwise-orthogonal source family `χ` of nonzero norm and a target family `X` matching its
Gram matrix (`⟨Xᵢ, Xⱼ⟩ = ⟨χᵢ, χⱼ⟩` — *not* orthonormality), the rescaled reconstruction
`ν = coherentImageMap χ (fun j => ⟨χⱼ, χⱼ⟩⁻¹ • Xⱼ)` sends `χₖ ↦ Xₖ`
(`coherentImageMap_apply_eq_of_orthogonal`) and preserves the inner product on `ℤ[range χ]`.

This is the `IsCoherent.extension_inner_eq` of a *non-orthonormal* equal-degree set — the shape
Peterfalvi's (5.7) needs once reducible members are allowed (issue 0157).  With `⟨χⱼ, χⱼ⟩ = 1`
it is `coherentImageMap_inner_eq`. -/
theorem coherentImageMapW_inner_eq [Fintype G] [Invertible (Nat.card G : ℂ)]
    {n : ℕ} {χ : Fin n → ClassFunction L ℂ} {X : Fin n → ClassFunction G ℂ}
    (horthχ : ∀ i j, i ≠ j → ClassFunction.inner (χ i) (χ j) = 0)
    (hnorm : ∀ j, ClassFunction.inner (χ j) (χ j) ≠ 0)
    (hgram : ∀ i j, ClassFunction.inner (X i) (X j) = ClassFunction.inner (χ i) (χ j))
    {φ ψ : ClassFunction L ℂ}
    (hφ : φ ∈ Submodule.span ℤ (Set.range χ)) (_hψ : ψ ∈ Submodule.span ℤ (Set.range χ)) :
    ClassFunction.inner
        (coherentImageMap (L := L) (G := G) χ
          (fun j => (ClassFunction.inner (χ j) (χ j))⁻¹ • X j) φ)
        (coherentImageMap (L := L) (G := G) χ
          (fun j => (ClassFunction.inner (χ j) (χ j))⁻¹ • X j) ψ) =
      ClassFunction.inner φ ψ := by
  classical
  rw [inner_eq_sum_inner_mul_conj_div_norm horthχ hnorm hφ, coherentImageMap_apply,
    coherentImageMap_apply, inner_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ClassFunction.inner_smul_left, inner_sum_right]
  rw [Finset.sum_eq_single j]
  · rw [OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_smul_right, ClassFunction.inner_smul_left,
      hgram j j]
    have hstar : star ((ClassFunction.inner (χ j) (χ j))⁻¹) =
        (ClassFunction.inner (χ j) (χ j))⁻¹ := by
      rw [star_inv₀, ← inner_conj_symm (χ j) (χ j)]
    rw [hstar]
    field_simp
  · intro k _ hkj
    rw [OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_smul_right, ClassFunction.inner_smul_left,
      hgram j k, horthχ j k fun h => hkj h.symm]
    ring
  · intro h; exact absurd (Finset.mem_univ j) h

end IntegralCharacterMap

end OddOrder.Peterfalvi.S07


