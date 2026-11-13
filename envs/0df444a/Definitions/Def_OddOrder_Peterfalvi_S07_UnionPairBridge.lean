-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_UnionPairBridge
-- name    : OddOrder_Peterfalvi_S07_UnionPairBridge
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:11:46.594206+00:00
-- url     : https://prove2.me/theorems/52cbfd18-3232-4c4c-a79b-04ef8ff67fbf
-- title:
--   Peterfalvi (5.6.3)/(9.11.7)–(9.11.8): union-pair coherent extension and projection budget
-- statement:
--   Formalizes the union-pair coherent extension (Peterfalvi, *Character Theory for the Odd Order Theorem*, §5 (5.6.3)) and the projection budget used in §9 (9.11.7)–(9.11.8).
--
--   Main declarations: `unionPairExtension` (The Fourier-projection extension of the union family `S ∪ {λ, λ̄}`); `isCoherent_union_pair_of_bridge` (The union-pair coherent extension); `exists_bridge_target_of_budget` (Peterfalvi (9.11.7)–(9.11.8), the projection budget).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_UnionPairBridge.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_UnionPairBridge.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_PivotCoherence

namespace OddOrder.Peterfalvi.S07

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

section UnionPair

variable {L Γ' : Type*} [Group L] [Group Γ']

variable [Fintype L] [Fintype Γ'] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card Γ' : ℂ)]

/-- The Fourier-projection extension of the union family `S ∪ {λ, λ̄}`: on the orthonormal
basis it sends `ψ ∈ S ↦ τ₁ψ`, `λ ↦ X`, `λ̄ ↦ Xc`.  A `ℤ`-linear map since each coefficient
functional `⟨·, η⟩` is (`IntegralCharacterMap.innerLeftℤ`). -/
noncomputable def unionPairExtension {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L Γ')
    (lam : ClassFunction L ℂ) (X Xc : ClassFunction Γ' ℂ) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap L Γ' :=
  (∑ ψ ∈ hSfin.toFinset,
      (OddOrder.Peterfalvi.S07.IntegralCharacterMap.innerLeftℤ ψ).smulRight (τ₁ ψ))
    + (OddOrder.Peterfalvi.S07.IntegralCharacterMap.innerLeftℤ lam).smulRight X
    + (OddOrder.Peterfalvi.S07.IntegralCharacterMap.innerLeftℤ lam.conj).smulRight Xc

omit [Fintype Γ'] [Invertible (Nat.card Γ' : ℂ)] in
theorem unionPairExtension_apply {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L Γ')
    (lam : ClassFunction L ℂ) (X Xc : ClassFunction Γ' ℂ) (φ : ClassFunction L ℂ) :
    unionPairExtension hSfin τ₁ lam X Xc φ
      = (∑ ψ ∈ hSfin.toFinset, ClassFunction.inner φ ψ • τ₁ ψ)
        + ClassFunction.inner φ lam • X + ClassFunction.inner φ lam.conj • Xc := by
  simp [unionPairExtension, LinearMap.sum_apply, LinearMap.smulRight_apply]

set_option maxHeartbeats 800000 in
-- the four structure fields each run `Submodule.span_induction` over the union lattice with
-- inner-product rewriting per generator pair
/-- **The union-pair coherent extension** (Peterfalvi (5.6.3); Coq `extend_coherent_with`
`PFsection5.v:1059` + `bridge_coherent` `PFsection5.v:1000`, the shape reused in (9.11.8)).

Inputs: an orthonormal finite family `S` with a coherent-extension-style map `τ₁` (isometric
on pairs of members, agreeing with `τ` on the `A`-supported lattice, `ℤ[Irr]`-valued on
members); a conjugate pair `{λ, λ̄}` of orthonormal members orthogonal to `S`; orthonormal
targets `X, Xc ∈ ℤ[Irr Γ']` orthogonal to the `τ₁`-images with `(λ − λ̄)^τ = X − Xc`; and the
**bridge** `(λ − E·ψ₀)^τ = X − E·τ₁ψ₀` for a member `ψ₀ ∈ S`, with `λ − E·ψ₀`
`A`-supported.  Conclusion: `S ∪ {λ, λ̄}` is coherent via the Fourier-projection extension.

Agreement on the supported lattice: a supported `φ = y + a·λ + b·λ̄` rewrites as
`φ' + (a+b)·(λ − E·ψ₀) + b·(λ̄ − λ)` with `φ' = y + (a+b)E·ψ₀ ∈ ℤ[S]` supported (difference
of supported elements), and `τ` agrees with the extension on all three pieces. -/
noncomputable def isCoherent_union_pair_of_bridge
    {τ τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L Γ'}
    {S : Set (ClassFunction L ℂ)} {A : Set L} (hSfin : S.Finite)
    (hON1 : ∀ φ ∈ S, ClassFunction.inner φ φ = 1)
    (hON2 : ∀ φ ∈ S, ∀ ξ ∈ S, φ ≠ ξ → ClassFunction.inner φ ξ = 0)
    (hτ₁pair : ∀ φ ∈ S, ∀ ξ ∈ S,
      ClassFunction.inner (τ₁ φ) (τ₁ ξ) = ClassFunction.inner φ ξ)
    (hτ₁agrees : ∀ φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A, τ₁ φ = τ φ)
    (hτ₁Z : ∀ φ ∈ S, τ₁ φ ∈ ZIrr Γ')
    {lam : ClassFunction L ℂ}
    (hlamne : lam ≠ lam.conj)
    (hlam1 : ClassFunction.inner lam lam = 1)
    (hlamc1 : ClassFunction.inner lam.conj lam.conj = 1)
    (hlamlamc : ClassFunction.inner lam lam.conj = 0)
    (hSlam : ∀ φ ∈ S, ClassFunction.inner φ lam = 0)
    (hSlamc : ∀ φ ∈ S, ClassFunction.inner φ lam.conj = 0)
    {X Xc : ClassFunction Γ' ℂ}
    (hXX : ClassFunction.inner X X = 1)
    (hXcXc : ClassFunction.inner Xc Xc = 1)
    (hXXc : ClassFunction.inner X Xc = 0)
    (hXZ : X ∈ ZIrr Γ') (hXcZ : Xc ∈ ZIrr Γ')
    (hextX : ∀ φ ∈ S, ClassFunction.inner (τ₁ φ) X = 0)
    (hextXc : ∀ φ ∈ S, ClassFunction.inner (τ₁ φ) Xc = 0)
    (hdiff : τ (lam - lam.conj) = X - Xc)
    (hdiffsupp : ((lam - lam.conj : ClassFunction L ℂ)).support ⊆ A)
    {ψ₀ : ClassFunction L ℂ} (hψ₀S : ψ₀ ∈ S) {E : ℤ}
    (hbridge : τ (lam - E • ψ₀) = X - E • τ₁ ψ₀)
    (hbridgesupp : ((lam - E • ψ₀ : ClassFunction L ℂ)).support ⊆ A) :
    OddOrder.Peterfalvi.S07.IsCoherent τ (S ∪ {lam, lam.conj}) A := by
  classical
  -- generator membership dichotomy
  have hUmem : ∀ x, x ∈ S ∪ ({lam, lam.conj} : Set (ClassFunction L ℂ)) →
      x ∈ S ∨ x = lam ∨ x = lam.conj := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · rcases Set.mem_insert_iff.mp hx with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Set.mem_singleton_iff.mp h))
  -- reversed-slot orthogonalities
  have hlamS : ∀ φ ∈ S, ClassFunction.inner lam φ = 0 := fun φ hφ => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm φ lam, hSlam φ hφ, star_zero]
  have hlamcS : ∀ φ ∈ S, ClassFunction.inner lam.conj φ = 0 := fun φ hφ => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm φ lam.conj, hSlamc φ hφ, star_zero]
  have hlamclam : ClassFunction.inner lam.conj lam = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm lam lam.conj, hlamlamc, star_zero]
  have hXcX : ClassFunction.inner Xc X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm X Xc, hXXc, star_zero]
  have hXext : ∀ φ ∈ S, ClassFunction.inner X (τ₁ φ) = 0 := fun φ hφ => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (τ₁ φ) X, hextX φ hφ, star_zero]
  have hXcext : ∀ φ ∈ S, ClassFunction.inner Xc (τ₁ φ) = 0 := fun φ hφ => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (τ₁ φ) Xc, hextXc φ hφ, star_zero]
  -- generator values of the extension
  have hval_mem : ∀ ψ' ∈ S, unionPairExtension hSfin τ₁ lam X Xc ψ' = τ₁ ψ' := by
    intro ψ' hψ'
    rw [unionPairExtension_apply, hSlam ψ' hψ', hSlamc ψ' hψ', zero_smul, zero_smul,
      add_zero, add_zero,
      Finset.sum_eq_single ψ'
        (fun ψ hψ hne => by
          rw [hON2 ψ' hψ' ψ (hSfin.mem_toFinset.mp hψ) (Ne.symm hne), zero_smul])
        (fun h => absurd (hSfin.mem_toFinset.mpr hψ') h),
      hON1 ψ' hψ', one_smul]
  have hval_lam : unionPairExtension hSfin τ₁ lam X Xc lam = X := by
    rw [unionPairExtension_apply, hlam1, hlamlamc, one_smul, zero_smul, add_zero,
      Finset.sum_eq_zero
        (fun ψ hψ => by rw [hlamS ψ (hSfin.mem_toFinset.mp hψ), zero_smul]),
      zero_add]
  have hval_lamc : unionPairExtension hSfin τ₁ lam X Xc lam.conj = Xc := by
    rw [unionPairExtension_apply, hlamc1, hlamclam, one_smul, zero_smul, add_zero,
      Finset.sum_eq_zero
        (fun ψ hψ => by rw [hlamcS ψ (hSfin.mem_toFinset.mp hψ), zero_smul]),
      zero_add]
  -- the extension agrees with `τ₁` on `ℤ[S]`
  have hext_span : ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := L) S,
      unionPairExtension hSfin τ₁ lam X Xc φ = τ₁ φ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hval_mem x hx
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul n x _ hx => rw [map_smul, map_smul, hx]
  -- inner products on generator pairs
  have hgen : ∀ x, (x ∈ S ∨ x = lam ∨ x = lam.conj) →
      ∀ y, (y ∈ S ∨ y = lam ∨ y = lam.conj) →
      ClassFunction.inner (unionPairExtension hSfin τ₁ lam X Xc x)
          (unionPairExtension hSfin τ₁ lam X Xc y)
        = ClassFunction.inner x y := by
    intro x hx y hy
    rcases hx with hx | rfl | rfl <;> rcases hy with hy | rfl | rfl
    · rw [hval_mem x hx, hval_mem y hy]; exact hτ₁pair x hx y hy
    · rw [hval_mem x hx, hval_lam, hextX x hx, hSlam x hx]
    · rw [hval_mem x hx, hval_lamc, hextXc x hx, hSlamc x hx]
    · rw [hval_lam, hval_mem y hy, hXext y hy, hlamS y hy]
    · rw [hval_lam, hXX, hlam1]
    · rw [hval_lam, hval_lamc, hXXc, hlamlamc]
    · rw [hval_lamc, hval_mem y hy, hXcext y hy, hlamcS y hy]
    · rw [hval_lamc, hval_lam, hXcX, hlamclam]
    · rw [hval_lamc, hXcXc, hlamc1]
  -- inner products, one slot span-general
  have hrow : ∀ y, (y ∈ S ∨ y = lam ∨ y = lam.conj) →
      ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := L) (S ∪ {lam, lam.conj}),
      ClassFunction.inner (unionPairExtension hSfin τ₁ lam X Xc φ)
          (unionPairExtension hSfin τ₁ lam X Xc y)
        = ClassFunction.inner φ y := by
    intro y hy φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hgen x (hUmem x hx) y hy
    | zero => rw [map_zero, ClassFunction.inner_zero_left, ClassFunction.inner_zero_left]
    | add x z _ _ hx hz =>
        rw [map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left, hx, hz]
    | smul n x _ hx =>
        rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ n (unionPairExtension hSfin τ₁ lam X Xc x),
          ← Int.cast_smul_eq_zsmul ℂ n x, ClassFunction.inner_smul_left,
          ClassFunction.inner_smul_left, hx]
  refine
    { nonzero := ⟨lam - lam.conj,
        ⟨Submodule.sub_mem _
          (Submodule.subset_span (Or.inr (Set.mem_insert _ _)))
          (Submodule.subset_span (Or.inr (Set.mem_insert_of_mem _ rfl))),
          hdiffsupp⟩,
        sub_ne_zero.mpr hlamne⟩
      extension := unionPairExtension hSfin τ₁ lam X Xc
      extension_inner_eq := ?_
      extends_on_supported := ?_
      extension_mem_ZIrr := ?_ }
  · -- isometry on the union lattice: span-induct the right slot over `hrow`
    intro φ ψ hφ hψ
    induction hψ using Submodule.span_induction with
    | mem y hy => exact hrow y (hUmem y hy) φ hφ
    | zero => rw [map_zero, ClassFunction.inner_zero_right, ClassFunction.inner_zero_right]
    | add x z _ _ hx hz =>
        rw [map_add, ClassFunction.inner_add_right, ClassFunction.inner_add_right, hx, hz]
    | smul n x _ hx =>
        rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ n (unionPairExtension hSfin τ₁ lam X Xc x),
          ← Int.cast_smul_eq_zsmul ℂ n x,
          OddOrder.RepresentationTheory.inner_smul_right,
          OddOrder.RepresentationTheory.inner_smul_right, hx]
  · -- agreement with `τ` on the supported union lattice
    intro φ hφ
    obtain ⟨hφspan, hφsupp⟩ := hφ
    have hφsup : φ ∈ Submodule.span ℤ (S : Set (ClassFunction L ℂ)) ⊔
        Submodule.span ℤ ({lam, lam.conj} : Set (ClassFunction L ℂ)) := by
      rw [← Submodule.span_union]
      exact hφspan
    obtain ⟨y, hy, z, hz, hφeq⟩ := Submodule.mem_sup.mp hφsup
    obtain ⟨a, b, hzeq⟩ := Submodule.mem_span_pair.mp hz
    -- the recentered element `φ' = y + (a+b)E·ψ₀ ∈ ℤ[S]`
    set φ' : ClassFunction L ℂ :=
      φ - (a + b) • (lam - E • ψ₀) - b • (lam.conj - lam) with hφ'def
    have hφ'eq : φ' = y + ((a + b) * E) • ψ₀ := by
      rw [hφ'def, ← hφeq, ← hzeq]
      module
    have hφ'span : φ' ∈ OddOrder.Peterfalvi.S07.zSpan (L := L) S := by
      rw [hφ'eq]
      exact Submodule.add_mem _ hy
        (Submodule.smul_mem _ _ (Submodule.subset_span hψ₀S))
    have hφ'supp : φ'.support ⊆ A := by
      intro x hx
      rw [ClassFunction.mem_support] at hx
      by_contra hxA
      have h1 : φ x = 0 := by
        by_contra h
        exact hxA (hφsupp (ClassFunction.mem_support.mpr h))
      have h2 : (lam - E • ψ₀ : ClassFunction L ℂ) x = 0 := by
        by_contra h
        exact hxA (hbridgesupp (ClassFunction.mem_support.mpr h))
      have h3 : (lam - lam.conj : ClassFunction L ℂ) x = 0 := by
        by_contra h
        exact hxA (hdiffsupp (ClassFunction.mem_support.mpr h))
      apply hx
      have hval : φ' x
          = φ x - ((a + b : ℤ) : ℂ) * (lam - E • ψ₀ : ClassFunction L ℂ) x
            + ((b : ℤ) : ℂ) * (lam - lam.conj : ClassFunction L ℂ) x := by
        rw [hφ'def, ClassFunction.sub_apply, ClassFunction.sub_apply,
          ← Int.cast_smul_eq_zsmul ℂ (a + b) (lam - E • ψ₀ : ClassFunction L ℂ),
          ← Int.cast_smul_eq_zsmul ℂ b (lam.conj - lam : ClassFunction L ℂ),
          ClassFunction.smul_apply, ClassFunction.smul_apply]
        have hneg : (lam.conj - lam : ClassFunction L ℂ) x
            = -((lam - lam.conj : ClassFunction L ℂ) x) := by
          rw [ClassFunction.sub_apply, ClassFunction.sub_apply]
          ring
        rw [hneg]
        ring
      rw [hval, h1, h2, h3, mul_zero, mul_zero, sub_zero, add_zero]
    -- decompose and transport piecewise
    have hφdecomp : φ = φ' + (a + b) • (lam - E • ψ₀) + b • (lam.conj - lam) := by
      rw [hφ'def]
      abel
    have hextβ : unionPairExtension hSfin τ₁ lam X Xc (lam - E • ψ₀)
        = τ (lam - E • ψ₀) := by
      rw [map_sub, map_smul, hval_lam, hval_mem ψ₀ hψ₀S, hbridge]
    have hextD : unionPairExtension hSfin τ₁ lam X Xc (lam.conj - lam)
        = τ (lam.conj - lam) := by
      have hτD : τ (lam.conj - lam) = Xc - X := by
        rw [show (lam.conj - lam : ClassFunction L ℂ) = -(lam - lam.conj) from by abel,
          map_neg, hdiff]
        abel
      rw [hτD, map_sub, hval_lamc, hval_lam]
    calc unionPairExtension hSfin τ₁ lam X Xc φ
        = unionPairExtension hSfin τ₁ lam X Xc φ'
            + (a + b) • unionPairExtension hSfin τ₁ lam X Xc (lam - E • ψ₀)
            + b • unionPairExtension hSfin τ₁ lam X Xc (lam.conj - lam) := by
          conv_lhs => rw [hφdecomp]
          rw [map_add, map_add, map_smul, map_smul]
      _ = τ φ' + (a + b) • τ (lam - E • ψ₀) + b • τ (lam.conj - lam) := by
          rw [hext_span φ' hφ'span, hτ₁agrees φ' ⟨hφ'span, hφ'supp⟩, hextβ, hextD]
      _ = τ φ := by
          conv_rhs => rw [hφdecomp]
          rw [map_add, map_add, map_smul, map_smul]
  · -- `ℤ[Irr Γ']`-valued on the union lattice
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
        rcases hUmem x hx with hxS | rfl | rfl
        · rw [hval_mem x hxS]; exact hτ₁Z x hxS
        · rw [hval_lam]; exact hXZ
        · rw [hval_lamc]; exact hXcZ
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x z _ _ hx hz => rw [map_add]; exact Submodule.add_mem _ hx hz
    | smul n x _ hx => rw [map_smul]; exact Submodule.smul_mem _ n hx

end UnionPair

section ProjectionBudget

variable {Γ' : Type*} [Group Γ'] [Fintype Γ'] [Invertible (Nat.card Γ' : ℂ)]

set_option maxHeartbeats 1600000 in
-- orthonormal-projection bookkeeping: repeated `Finset` sum collapses and a final
-- integer-cast budget analysis
/-- **Peterfalvi (9.11.7)–(9.11.8), the projection budget** (Coq `PFsection9.v:2090-2172`
for (9.11.7) and `:2173-2220` for the `b`-elimination of (9.11.8)).

Abstract data: two orthonormal families `θ₁` (indexed by `SF`, `|SF| = 2e`, the
`𝒮₁^{τ₁}`-side) and `θ₃` (indexed by `S4F`, the `𝒮₄^{τ₃}`-side), mutually orthogonal;
`TB = β^τ` of norm `e² + 1` with integer coefficients, `θ₁`-coefficients constant off `ψ₁`
with offset `e` ((9.11.7): `⟨β, ψ − ψ₁⟩ = e`), and `θ₃ l₁/l₂`-coefficient difference `1`
(`⟨β, λ₁ − λ̄₁⟩ = 1`); `TA = α^τ` with `⟨TA, TB⟩ = e`, `TA ⊥ θ₃` ((9.11.6)), and
`θ₁`-coefficients constant off `ψ₁` with offset `1` (`⟨α, ψ − ψ₁⟩ = 1`).

Projecting `TB = Γ + B + Δ` on the two families, the norm budget
`‖Γ‖² + (b−e)² + (2e−1)b² + ‖Δ‖² = e² + 1` with `‖Γ‖² ≥ 1` (the `l₁/l₂` coefficients cannot
both vanish) forces `‖Γ‖² = 1`, `Δ = 0`, `b ∈ {0,1}` **(9.11.7)**; then
`e = ⟨TA, TB⟩ = (b−e)x + (2e−1)b(x+1)` forces `e·(x+1) = 1` if `b = 1` — impossible for
`e ≥ 2` — so `b = 0` **(9.11.8)** and `TB = Γ − e·θ₁ψ₁`. -/
theorem exists_bridge_target_of_budget {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {SF : Finset ι} {S4F : Finset κ}
    (θ₁ : ι → ClassFunction Γ' ℂ) (θ₃ : κ → ClassFunction Γ' ℂ)
    {TB TA : ClassFunction Γ' ℂ} {ψ₁ : ι} {l₁ l₂ : κ} {e : ℕ}
    (hψ₁SF : ψ₁ ∈ SF) (hl₁ : l₁ ∈ S4F) (hl₂ : l₂ ∈ S4F)
    (he2 : 2 ≤ e) (hcard : SF.card = 2 * e)
    (hON₁ : ∀ i ∈ SF, ∀ j ∈ SF,
      ClassFunction.inner (θ₁ i) (θ₁ j) = if i = j then 1 else 0)
    (hON₃ : ∀ i ∈ S4F, ∀ j ∈ S4F,
      ClassFunction.inner (θ₃ i) (θ₃ j) = if i = j then 1 else 0)
    (hcross : ∀ i ∈ SF, ∀ j ∈ S4F, ClassFunction.inner (θ₁ i) (θ₃ j) = 0)
    (hθ₃Z : ∀ j ∈ S4F, θ₃ j ∈ ZIrr Γ') (hθ₁Z : ∀ i ∈ SF, θ₁ i ∈ ZIrr Γ')
    (hTBZ : TB ∈ ZIrr Γ')
    (hTBnorm : ClassFunction.inner TB TB = ((e : ℂ)) ^ 2 + 1)
    (hTBconst : ∀ i ∈ SF, i ≠ ψ₁ →
      ClassFunction.inner TB (θ₁ i) = ClassFunction.inner TB (θ₁ ψ₁) + (e : ℂ))
    (hTBD : ClassFunction.inner TB (θ₃ l₁) - ClassFunction.inner TB (θ₃ l₂) = 1)
    (hTATB : ClassFunction.inner TA TB = (e : ℂ))
    (hTAθ₃ : ∀ j ∈ S4F, ClassFunction.inner TA (θ₃ j) = 0)
    (hTAconst : ∀ i ∈ SF, i ≠ ψ₁ →
      ClassFunction.inner TA (θ₁ i) = ClassFunction.inner TA (θ₁ ψ₁) + 1)
    (hTAψ₁int : ∃ m : ℤ, ClassFunction.inner TA (θ₁ ψ₁) = (m : ℂ))
    (hTBψ₁int : ∃ m : ℤ, ClassFunction.inner TB (θ₁ ψ₁) = (m : ℂ))
    (hTBθ₃int : ∀ j ∈ S4F, ∃ m : ℤ, ClassFunction.inner TB (θ₃ j) = (m : ℂ)) :
    ∃ X : ClassFunction Γ' ℂ, X ∈ ZIrr Γ' ∧
      ClassFunction.inner X X = 1 ∧
      (∀ i ∈ SF, ClassFunction.inner (θ₁ i) X = 0) ∧
      ClassFunction.inner X (θ₃ l₁) - ClassFunction.inner X (θ₃ l₂) = 1 ∧
      TB = X - (e : ℂ) • θ₁ ψ₁ := by
  classical
  choose! mΓ hmΓ using hTBθ₃int
  obtain ⟨mψ, hmψ⟩ := hTBψ₁int
  -- the three projection components
  set Γ0 : ClassFunction Γ' ℂ :=
    ∑ j ∈ S4F, ClassFunction.inner TB (θ₃ j) • θ₃ j with hΓ0
  set B0 : ClassFunction Γ' ℂ :=
    ∑ i ∈ SF, ClassFunction.inner TB (θ₁ i) • θ₁ i with hB0
  set Δ0 : ClassFunction Γ' ℂ := TB - Γ0 - B0 with hΔ0
  -- sum expansions
  have hΓ0L : ∀ ψ : ClassFunction Γ' ℂ, ClassFunction.inner Γ0 ψ
      = ∑ j ∈ S4F, ClassFunction.inner TB (θ₃ j) * ClassFunction.inner (θ₃ j) ψ := by
    intro ψ
    rw [hΓ0, OddOrder.RepresentationTheory.inner_sum_left]
    exact Finset.sum_congr rfl fun j _ => by rw [ClassFunction.inner_smul_left]
  have hΓ0R : ∀ ψ : ClassFunction Γ' ℂ, ClassFunction.inner ψ Γ0
      = ∑ j ∈ S4F, star (ClassFunction.inner TB (θ₃ j)) * ClassFunction.inner ψ (θ₃ j) := by
    intro ψ
    rw [hΓ0, OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_congr rfl fun j _ => by
      rw [OddOrder.RepresentationTheory.inner_smul_right]
  have hB0L : ∀ ψ : ClassFunction Γ' ℂ, ClassFunction.inner B0 ψ
      = ∑ i ∈ SF, ClassFunction.inner TB (θ₁ i) * ClassFunction.inner (θ₁ i) ψ := by
    intro ψ
    rw [hB0, OddOrder.RepresentationTheory.inner_sum_left]
    exact Finset.sum_congr rfl fun i _ => by rw [ClassFunction.inner_smul_left]
  have hB0R : ∀ ψ : ClassFunction Γ' ℂ, ClassFunction.inner ψ B0
      = ∑ i ∈ SF, star (ClassFunction.inner TB (θ₁ i)) * ClassFunction.inner ψ (θ₁ i) := by
    intro ψ
    rw [hB0, OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_congr rfl fun i _ => by
      rw [OddOrder.RepresentationTheory.inner_smul_right]
  -- projections onto the two families
  have hΓ0proj : ∀ j₀ ∈ S4F, ClassFunction.inner Γ0 (θ₃ j₀)
      = ClassFunction.inner TB (θ₃ j₀) := by
    intro j₀ hj₀
    rw [hΓ0L (θ₃ j₀),
      Finset.sum_eq_single j₀
        (fun j hj hne => by rw [hON₃ j hj j₀ hj₀, if_neg hne, mul_zero])
        (fun h => absurd hj₀ h),
      hON₃ j₀ hj₀ j₀ hj₀, if_pos rfl, mul_one]
  have hB0proj : ∀ i₀ ∈ SF, ClassFunction.inner B0 (θ₁ i₀)
      = ClassFunction.inner TB (θ₁ i₀) := by
    intro i₀ hi₀
    rw [hB0L (θ₁ i₀),
      Finset.sum_eq_single i₀
        (fun i hi hne => by rw [hON₁ i hi i₀ hi₀, if_neg hne, mul_zero])
        (fun h => absurd hi₀ h),
      hON₁ i₀ hi₀ i₀ hi₀, if_pos rfl, mul_one]
  have hB0θ₃ : ∀ j ∈ S4F, ClassFunction.inner B0 (θ₃ j) = 0 := by
    intro j hj
    rw [hB0L (θ₃ j)]
    exact Finset.sum_eq_zero fun i hi => by rw [hcross i hi j hj, mul_zero]
  have hΓ0θ₁ : ∀ i ∈ SF, ClassFunction.inner Γ0 (θ₁ i) = 0 := by
    intro i hi
    rw [hΓ0L (θ₁ i)]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [OddOrder.RepresentationTheory.inner_conj_symm (θ₁ i) (θ₃ j), hcross i hi j hj,
      star_zero, mul_zero]
  have hθ₁Γ0 : ∀ i ∈ SF, ClassFunction.inner (θ₁ i) Γ0 = 0 := by
    intro i hi
    rw [hΓ0R (θ₁ i)]
    exact Finset.sum_eq_zero fun j hj => by rw [hcross i hi j hj, mul_zero]
  -- the residual is orthogonal to both families
  have hΔθ₃ : ∀ j ∈ S4F, ClassFunction.inner Δ0 (θ₃ j) = 0 := by
    intro j hj
    rw [hΔ0, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      hΓ0proj j hj, hB0θ₃ j hj, sub_zero, sub_self]
  have hΔθ₁ : ∀ i ∈ SF, ClassFunction.inner Δ0 (θ₁ i) = 0 := by
    intro i hi
    rw [hΔ0, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      hΓ0θ₁ i hi, hB0proj i hi, sub_zero, sub_self]
  -- the split `TB = Γ0 + B0 + Δ0`
  have hTBsplit : TB = Γ0 + B0 + Δ0 := by rw [hΔ0]; abel
  -- cross inner products vanish
  have hΓ0B0 : ClassFunction.inner Γ0 B0 = 0 := by
    rw [hB0R Γ0]
    exact Finset.sum_eq_zero fun i hi => by rw [hΓ0θ₁ i hi, mul_zero]
  have hB0Γ0 : ClassFunction.inner B0 Γ0 = 0 := by
    rw [hΓ0R B0]
    exact Finset.sum_eq_zero fun j hj => by rw [hB0θ₃ j hj, mul_zero]
  have hΔ0Γ0 : ClassFunction.inner Δ0 Γ0 = 0 := by
    rw [hΓ0R Δ0]
    exact Finset.sum_eq_zero fun j hj => by rw [hΔθ₃ j hj, mul_zero]
  have hΓ0Δ0 : ClassFunction.inner Γ0 Δ0 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm Δ0 Γ0, hΔ0Γ0, star_zero]
  have hΔ0B0 : ClassFunction.inner Δ0 B0 = 0 := by
    rw [hB0R Δ0]
    exact Finset.sum_eq_zero fun i hi => by rw [hΔθ₁ i hi, mul_zero]
  have hB0Δ0 : ClassFunction.inner B0 Δ0 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm Δ0 B0, hΔ0B0, star_zero]
  -- Pythagoras
  have hPyth : ClassFunction.inner TB TB
      = ClassFunction.inner Γ0 Γ0 + ClassFunction.inner B0 B0
        + ClassFunction.inner Δ0 Δ0 := by
    conv_lhs => rw [hTBsplit]
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_left,
      ClassFunction.inner_add_right, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, ClassFunction.inner_add_right,
      hΓ0B0, hB0Γ0, hΔ0Γ0, hΓ0Δ0, hΔ0B0, hB0Δ0]
    ring
  -- `‖Γ0‖² = ∑ mΓ²`
  have hΓ0norm : ClassFunction.inner Γ0 Γ0 = ((∑ j ∈ S4F, mΓ j ^ 2 : ℤ) : ℂ) := by
    rw [hΓ0R Γ0, Int.cast_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hΓ0proj j hj, hmΓ j hj, star_intCast]
    push_cast
    ring
  -- `‖B0‖² = mψ² + (2e−1)(mψ+e)²`
  have hbval : ∀ i ∈ SF, i ≠ ψ₁ →
      ClassFunction.inner TB (θ₁ i) = ((mψ + (e : ℤ) : ℤ) : ℂ) := by
    intro i hi hne
    rw [hTBconst i hi hne, hmψ]
    push_cast
    ring
  have hB0norm : ClassFunction.inner B0 B0
      = ((mψ ^ 2 + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) ^ 2 : ℤ) : ℂ) := by
    rw [hB0R B0, ← Finset.add_sum_erase SF _ hψ₁SF]
    have herase : ∀ i ∈ SF.erase ψ₁,
        star (ClassFunction.inner TB (θ₁ i)) * ClassFunction.inner B0 (θ₁ i)
          = (((mψ + (e : ℤ)) ^ 2 : ℤ) : ℂ) := by
      intro i hi
      have hiSF := Finset.mem_of_mem_erase hi
      have hine := Finset.ne_of_mem_erase hi
      rw [hB0proj i hiSF, hbval i hiSF hine, star_intCast]
      push_cast
      ring
    rw [Finset.sum_congr rfl herase, Finset.sum_const, Finset.card_erase_of_mem hψ₁SF,
      hcard, hB0proj ψ₁ hψ₁SF, hmψ, star_intCast, nsmul_eq_mul,
      Nat.cast_sub (show 1 ≤ 2 * e from by omega)]
    push_cast
    ring
  -- `‖Δ0‖²` is a nonnegative integer
  have hΔ0Z : Δ0 ∈ ZIrr Γ' := by
    rw [hΔ0]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hTBZ ?_) ?_
    · rw [hΓ0]
      refine Submodule.sum_mem _ fun j hj => ?_
      rw [hmΓ j hj, Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (hθ₃Z j hj)
    · rw [hB0]
      refine Submodule.sum_mem _ fun i hi => ?_
      by_cases hne : i = ψ₁
      · subst hne
        rw [hmψ, Int.cast_smul_eq_zsmul]
        exact Submodule.smul_mem _ _ (hθ₁Z i hi)
      · rw [hbval i hi hne, Int.cast_smul_eq_zsmul]
        exact Submodule.smul_mem _ _ (hθ₁Z i hi)
  obtain ⟨cΔ, -, -, hcΔsum⟩ :=
    OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq hΔ0Z
  have hΔval : ClassFunction.inner Δ0 Δ0
      = ((∑ x ∈ cΔ.support, cΔ x ^ 2 : ℤ) : ℂ) := by
    rw [hcΔsum]
    push_cast
    rfl
  have hsΔ0 : 0 ≤ ∑ x ∈ cΔ.support, cΔ x ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- `‖Γ0‖² ≥ 1`: the `l₁`/`l₂` coefficients differ by `1`
  have hmΓD : mΓ l₁ - mΓ l₂ = 1 := by
    have h : ((mΓ l₁ - mΓ l₂ : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
      push_cast
      rw [← hmΓ l₁ hl₁, ← hmΓ l₂ hl₂]
      exact_mod_cast hTBD
    exact_mod_cast h
  have hsq1 : ∀ m : ℤ, m ≠ 0 → 1 ≤ m ^ 2 := by
    intro m hm
    rcases lt_or_gt_of_ne hm with h | h <;> nlinarith
  have hsΓ1 : 1 ≤ ∑ j ∈ S4F, mΓ j ^ 2 := by
    rcases eq_or_ne (mΓ l₁) 0 with h1 | h1
    · have h2 : mΓ l₂ ≠ 0 := by omega
      exact le_trans (hsq1 _ h2)
        (Finset.single_le_sum (fun j _ => sq_nonneg (mΓ j)) hl₂)
    · exact le_trans (hsq1 _ h1)
        (Finset.single_le_sum (fun j _ => sq_nonneg (mΓ j)) hl₁)
  -- the integer budget
  have hbudget : (e : ℤ) ^ 2 + 1
      = (∑ j ∈ S4F, mΓ j ^ 2) + (mψ ^ 2 + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) ^ 2)
        + ∑ x ∈ cΔ.support, cΔ x ^ 2 := by
    have h : (((e : ℤ) ^ 2 + 1 : ℤ) : ℂ)
        = (((∑ j ∈ S4F, mΓ j ^ 2) + (mψ ^ 2 + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) ^ 2)
            + ∑ x ∈ cΔ.support, cΔ x ^ 2 : ℤ) : ℂ) := by
      push_cast
      rw [show ((e : ℂ)) ^ 2 + 1 = ClassFunction.inner TB TB from hTBnorm.symm, hPyth,
        hΓ0norm, hB0norm, hΔval]
      push_cast
      ring
    exact_mod_cast h
  -- pin the budget: `‖Γ0‖² = 1`, `mb(mb−1) = 0`, `‖Δ0‖² = 0`
  have hmb4 : -1 ≤ 4 * ((mψ + (e : ℤ)) * ((mψ + (e : ℤ)) - 1)) := by
    nlinarith [sq_nonneg (2 * (mψ + (e : ℤ)) - 1)]
  have hmbnn : 0 ≤ (mψ + (e : ℤ)) * ((mψ + (e : ℤ)) - 1) := by omega
  have hbudget' : 1 = (∑ j ∈ S4F, mΓ j ^ 2)
      + 2 * (e : ℤ) * ((mψ + (e : ℤ)) * ((mψ + (e : ℤ)) - 1))
      + ∑ x ∈ cΔ.support, cΔ x ^ 2 := by linear_combination hbudget
  have heZ2 : (2 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he2
  have h2emb : 0 ≤ 2 * (e : ℤ) * ((mψ + (e : ℤ)) * ((mψ + (e : ℤ)) - 1)) := by positivity
  have hsΓeq : ∑ j ∈ S4F, mΓ j ^ 2 = 1 := by linarith
  have h2emb0 : 2 * (e : ℤ) * ((mψ + (e : ℤ)) * ((mψ + (e : ℤ)) - 1)) = 0 := by linarith
  have hsΔeq : ∑ x ∈ cΔ.support, cΔ x ^ 2 = 0 := by linarith
  have hmb01 : mψ + (e : ℤ) = 0 ∨ mψ + (e : ℤ) = 1 := by
    have h := mul_eq_zero.mp
      ((mul_eq_zero.mp h2emb0).resolve_left (by omega : ¬ 2 * (e : ℤ) = 0))
    omega
  -- `Δ0 = 0`
  have hΔzero : Δ0 = 0 := by
    apply OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero
    rw [hΔval, hsΔeq]
    simp
  -- (9.11.8): the `⟨TA, TB⟩ = e` pairing eliminates `mb = 1`
  obtain ⟨mx, hmx⟩ := hTAψ₁int
  have hTAB0 : ClassFunction.inner TA B0
      = ((mψ * mx + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) * (mx + 1) : ℤ) : ℂ) := by
    rw [hB0R TA, ← Finset.add_sum_erase SF _ hψ₁SF]
    have herase : ∀ i ∈ SF.erase ψ₁,
        star (ClassFunction.inner TB (θ₁ i)) * ClassFunction.inner TA (θ₁ i)
          = (((mψ + (e : ℤ)) * (mx + 1) : ℤ) : ℂ) := by
      intro i hi
      have hiSF := Finset.mem_of_mem_erase hi
      have hine := Finset.ne_of_mem_erase hi
      rw [hbval i hiSF hine, hTAconst i hiSF hine, hmx, star_intCast]
      push_cast
      ring
    rw [Finset.sum_congr rfl herase, Finset.sum_const, Finset.card_erase_of_mem hψ₁SF,
      hcard, hmψ, hmx, star_intCast, nsmul_eq_mul,
      Nat.cast_sub (show 1 ≤ 2 * e from by omega)]
    push_cast
    ring
  have hTAΓ0 : ClassFunction.inner TA Γ0 = 0 := by
    rw [hΓ0R TA]
    exact Finset.sum_eq_zero fun j hj => by rw [hTAθ₃ j hj, mul_zero]
  have hpairing : (e : ℤ) = mψ * mx + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) * (mx + 1) := by
    have h : ((e : ℤ) : ℂ)
        = ((mψ * mx + (2 * (e : ℤ) - 1) * (mψ + (e : ℤ)) * (mx + 1) : ℤ) : ℂ) := by
      rw [show ((e : ℤ) : ℂ) = (e : ℂ) from by push_cast; rfl, ← hTATB]
      conv_lhs => rw [hTBsplit]
      rw [ClassFunction.inner_add_right, ClassFunction.inner_add_right, hTAΓ0,
        hΔzero, ClassFunction.inner_zero_right, add_zero, zero_add, hTAB0]
    exact_mod_cast h
  have hmb0 : mψ + (e : ℤ) = 0 := by
    rcases hmb01 with h | h
    · exact h
    · exfalso
      -- `mb = 1` forces `e·(mx+1) = 1`, impossible for `e ≥ 2`
      have hmψe : mψ = 1 - (e : ℤ) := by omega
      have hkey : (e : ℤ) * (mx + 1) = 1 := by
        rw [hmψe] at hpairing
        linear_combination -hpairing
      have hdvd : (e : ℤ) ∣ 1 := ⟨mx + 1, hkey.symm⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
  -- the `b = 0` bridge: `B0 = −e·θ₁ψ₁` and `TB = Γ0 − e·θ₁ψ₁`
  have hB0eq : B0 = -(e : ℂ) • θ₁ ψ₁ := by
    rw [hB0,
      Finset.sum_eq_single ψ₁
        (fun i hi hne => by
          rw [hbval i hi hne, show mψ + (e : ℤ) = 0 from hmb0, Int.cast_zero, zero_smul])
        (fun h => absurd hψ₁SF h),
      hmψ, show mψ = -(e : ℤ) from by omega]
    push_cast
    ring_nf
  have hTBfinal : TB = Γ0 - (e : ℂ) • θ₁ ψ₁ := by
    rw [hTBsplit, hΔzero, hB0eq]
    module
  -- assemble the output
  refine ⟨Γ0, ?_, ?_, hθ₁Γ0, ?_, hTBfinal⟩
  · rw [hΓ0]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [hmΓ j hj, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (hθ₃Z j hj)
  · rw [hΓ0norm, hsΓeq]
    simp
  · rw [hΓ0proj l₁ hl₁, hΓ0proj l₂ hl₂]
    exact hTBD

end ProjectionBudget

end OddOrder.Peterfalvi.S07


