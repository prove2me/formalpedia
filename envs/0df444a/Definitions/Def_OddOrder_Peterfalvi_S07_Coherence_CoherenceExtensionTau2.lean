-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceExtensionTau2
-- name    : OddOrder_Peterfalvi_S07_Coherence_CoherenceExtensionTau2
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:36.216211+00:00
-- url     : https://prove2.me/theorems/047c8c1a-e8d0-48ed-89ec-d21482920a39
-- title:
--   Peterfalvi (5.6.3)/(5.6.2)/(5.5): the coherence-union extension $\tau_2$ and its images
-- statement:
--   The $\tau_2$ extension used in Peterfalvi (5.6.3)/(5.6.2)/(5.5), together with the image-equation supplier and the orthogonality of the running images to $R(\chi)$.
--
--   Main definitions: `retarget_isCoherent` (Peterfalvi (5.6.3): coherence of $S_1\cup\{\chi,\bar\chi\}$), `coherentEqualDegree` (Peterfalvi (1.1)+(1.4): an equal-degree set is coherent), `coherentEqualDegreeW` (Peterfalvi (5.7) core: equal degree with arbitrary member norms), `coherentEqualDegree_swap_neg` (sign-swap relabelling of a coherence witness) and `inner_extension_member_orthogonal_imageSet` (the per-member orthogonality $\chi'^{\tau_1}\perp R(\chi)$).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_Coherence/CoherenceExtensionTau2.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_Coherence/CoherenceExtensionTau2.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

open IntegralCharacterMap in
/-- **Peterfalvi (5.6.3): coherence of `S₁ ∪ {χ, χ̄}`.**

Given a coherent `τ` on `S₁` (witness `hS₁`, with `τ₁ := hS₁.extension`), an orthonormal pair
`{χ, χ̄}` disjoint from and orthogonal to `S₁`, and the (5.4)/(5.5)/(5.6.2) target data `{X, X̄}`
— orthonormal in `ℤ[Irr G]`, with `X̄ = X − (χ − χ̄)^τ`, both orthogonal to `τ₁ ξ` for every `ξ`
orthogonal to `{χ, χ̄}` (the (5.5)+(5.2.e) input), and with the (5.6.2) image equation
`(χ − a·χ₁)^τ = X − a·χ₁^{τ₁}` — the union `S₁ ∪ {χ, χ̄}` is coherent.

The constructed extension is `τ₂ := retarget τ₁ χ χ̄ X X̄`: it is a global integral isometry by the
keystone `retarget_isIntegralIsometry`, sends `χ ↦ X`, `χ̄ ↦ X̄`, keeps `τ₁` off `{χ, χ̄}`, and
agrees with `τ` on the supported span — checked on the three difference generators
`{χ − χ̄, χ − a·χ₁} ∪ Z[S₁, L^#]` via `eq_on_zSpan_of_eq_on`, using the generation hypothesis
`hgen`.  The degree ratio `a : ℕ` (`χ(1) = a·χ₁(1)` from hypothesis (b) divisibility,
`exists_pos_natDegreeRatio_of_dvd`) enters as a *natural* scalar, so the difference `χ − a·χ₁`
is preserved by the `ℤ`-linear `τ₂`. -/
noncomputable def retarget_isCoherent
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ chibar chi1 : ClassFunction L ℂ} {a : ℕ} {X Xbar : ClassFunction G ℂ}
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hXX : ClassFunction.inner X X = 1) (hXbarXbar : ClassFunction.inner Xbar Xbar = 1)
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
  set τ₂ := retarget τ₁ χ chibar X Xbar with hτ₂def
  -- χ, χ̄ are orthogonal to all of ℤ[S₁].
  have hχ_zspan : ∀ φ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ S₁ →
      ClassFunction.inner χ φ = 0 := fun φ hφ =>
    IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hφ
  have hχbar_zspan : ∀ φ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ S₁ →
      ClassFunction.inner chibar φ = 0 := fun φ hφ =>
    IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχbar_S1 hφ
  -- (1) τ₂ preserves `⟨·,·⟩` on the *lattice* `ℤ[S₁ ∪ {χ, χ̄}]` (the genuine (5.6.3) isometry).
  -- This uses only the `ℤ[S₁]`-isometry of `τ₁ = hS₁.extension` (the coherence of `S₁`) and the
  -- honest lattice orthogonality `X, X̄ ⊥ τ₁ ξ` for `ξ ∈ ℤ[S₁]`; *not* a global isometry.
  have hτ₂_inner : ∀ φ ψ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) (S₁ ∪ {χ, chibar}) → ψ ∈ zSpan (L := L) (S₁ ∪ {χ, chibar}) →
      ClassFunction.inner (τ₂ φ) (τ₂ ψ) = ClassFunction.inner φ ψ := by
    intro φ ψ hφ hψ
    rw [hτ₂def]
    exact retarget_inner_eq_on_zSpan_union hS₁.extension_inner_eq hχχ hχbarχbar hχχbar hχbarχ
      hXX hXbarXbar hXXbar hXbarX hχ_S1 hχbar_S1 hX_ortho hXbar_ortho hφ hψ
  -- (2) Agreement of τ₂ with τ on the three difference generators.
  -- (2a) On χ - χ̄: τ₂(χ-χ̄) = X - X̄ = X - (X - τ(χ-χ̄)) = τ(χ-χ̄).
  have hagree_diff : τ₂ (χ - chibar) = τ (χ - chibar) := by
    rw [hτ₂def, map_sub, retarget_apply_left hχχ hχχbar, retarget_apply_right hχbarχ hχbarχbar,
      hXbar_def]; abel
  -- (2b) On χ - a·χ₁: τ₂(χ - a•χ₁) = X - a•τ₁χ₁ = τ(χ - a•χ₁).
  have hagree_ratio : τ₂ (χ - a • chi1) = τ (χ - a • chi1) := by
    have hχ₁ : τ₂ chi1 = τ₁ chi1 :=
      retarget_eq_of_orthogonal
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 chi1 hchi1, star_zero])
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 chi1 hchi1, star_zero])
    rw [hτ₂def, map_sub, map_nsmul, retarget_apply_left hχχ hχχbar, ← hτ₂def, hχ₁,
      himg, hτ₁def]
  -- (2c) On Z[S₁, L^#]: τ₂ φ = τ₁ φ = τ φ.
  have hagree_S1 : ∀ x ∈ zSupportedSpan (L := L) S₁ A, τ₂ x = τ x := by
    intro x hx
    have hxspan : x ∈ Submodule.span ℤ S₁ := hx.1
    have hτ₂x : τ₂ x = τ₁ x := by
      rw [hτ₂def]
      exact retarget_eq_of_orthogonal
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_zspan x hxspan, star_zero])
        (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_zspan x hxspan, star_zero])
    rw [hτ₂x, hτ₁def, hS₁.extends_on_supported x hx]
  -- (3) τ₂ = τ on the generating set T, hence on its span (eq_on_zSpan_of_eq_on).
  have hagree_T : ∀ y ∈ zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1},
      τ₂ y = τ y := by
    intro y hy
    rcases hy with hyS1 | hypair
    · exact hagree_S1 y hyS1
    · rcases hypair with hy1 | hy2
      · rw [hy1]; exact hagree_diff
      · rw [hy2]; exact hagree_ratio
  -- (4) Assemble the IsCoherent witness.
  refine ⟨?_, τ₂, hτ₂_inner, ?_, ?_⟩
  · -- nonzero: inherited from S₁ ⊆ S₁ ∪ {χ, χ̄}.
    obtain ⟨φ, hφmem, hφne⟩ := hS₁.nonzero
    exact ⟨φ, zSupportedSpan_mono_left (Set.subset_union_left) hφmem, hφne⟩
  · -- extends_on_supported via span generation + generator agreement.
    intro φ hφ
    exact IntegralCharacterMap.eq_on_zSpan_of_eq_on hagree_T (hgen hφ)
  · -- extension_mem_ZIrr: `τ₂ = retarget τ₁ χ χ̄ X X̄` sends each generator of `ℤ[S₁ ∪ {χ, χ̄}]` to
    -- a virtual character (`S₁`-members via `τ₁` and its inductive ZIrr-codomain; `χ ↦ X`,
    -- `χ̄ ↦ X̄`).
    intro φ hφ
    rw [hτ₂def]
    induction hφ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hyS1 | hyχ
        · rw [retarget_eq_of_orthogonal
              (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 y hyS1, star_zero])
              (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 y hyS1, star_zero]),
            hτ₁def]
          exact hS₁.extension_mem_ZIrr y (Submodule.subset_span hyS1)
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hyχ
          rcases hyχ with rfl | rfl
          · rw [retarget_apply_left hχχ hχχbar]; exact hXZ
          · rw [retarget_apply_right hχbarχ hχbarχbar]; exact hXbarZ
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul c y _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ c ih

/-- **Equal-degree generation:** every supported `φ ∈ ℤ[range χ, A]` is an integer combination of
the differences `χⱼ − χ₀`.  Since all `χⱼ` share the value `d ≠ 0` at `1 ∉ A`, a supported
combination `∑ⱼ cⱼ χⱼ` vanishes at `1`, forcing `∑ⱼ cⱼ = 0`, so it equals `∑ⱼ cⱼ (χⱼ − χ₀)`.  This
is the `n`-element analogue of `zSupportedSpan_pair_subset_span` (the base of (6.6)/(6.8)). -/
theorem zSupportedSpan_range_subset_span_sub_zero {n : ℕ} [NeZero n]
    {χ : Fin n → ClassFunction L ℂ} {A : Set L}
    (hdeg : ∀ j, ((χ j : ClassFunction L ℂ) : L → ℂ) 1 = ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A) :
    zSupportedSpan (L := L) (Set.range χ) A ⊆
      Submodule.span ℤ (Set.range (fun j => χ j - χ 0)) := by
  classical
  intro φ hφ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).mp hφ.1
  have hφ1 : φ (1 : L) = 0 := by
    by_contra h
    exact h1A (hφ.2 (ClassFunction.mem_support.mpr h))
  have hc' : ∑ j : Fin n, (c j : ℂ) • χ j = φ := by
    rw [← hc]
    exact Finset.sum_congr rfl fun j _ => Int.cast_smul_eq_zsmul ℂ (c j) (χ j)
  have heval : ∑ j : Fin n, (c j : ℂ) * ((χ j : ClassFunction L ℂ) : L → ℂ) 1 = 0 := by
    have h := congrArg (fun ψ : ClassFunction L ℂ => ψ (1 : L)) hc'
    simpa [classFunction_sum_apply, ClassFunction.smul_apply, hφ1] using h
  have hsum0 : ∑ j : Fin n, c j = 0 := by
    have hrw : ∑ j : Fin n, (c j : ℂ) * ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1
        = ∑ j : Fin n, (c j : ℂ) * ((χ j : ClassFunction L ℂ) : L → ℂ) 1 :=
      Finset.sum_congr rfl fun j _ => by rw [hdeg j]
    have key : (∑ j : Fin n, (c j : ℂ)) * ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1 = 0 := by
      rw [Finset.sum_mul, hrw, heval]
    have hsum0ℂ : (∑ j : Fin n, (c j : ℂ)) = 0 := (mul_eq_zero.mp key).resolve_right hdeg0
    have hcast : ((∑ j : Fin n, c j : ℤ) : ℂ) = ∑ j : Fin n, (c j : ℂ) := by push_cast; ring
    exact_mod_cast hcast.trans hsum0ℂ
  rw [← hc]
  have heq : ∑ j : Fin n, c j • χ j = ∑ j : Fin n, c j • (χ j - χ 0) := by
    have hexp : ∑ j : Fin n, c j • (χ j - χ 0)
        = (∑ j : Fin n, c j • χ j) - (∑ j : Fin n, c j) • χ 0 := by
      rw [Finset.sum_smul]
      simp only [smul_sub]
      rw [Finset.sum_sub_distrib]
    rw [hexp, hsum0, zero_smul, sub_zero]
  rw [heq]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

open IntegralCharacterMap in
/-- **Peterfalvi (1.1)+(1.4): an equal-degree set is coherent.**

If `χ : Fin n → CF(L)` (`n ≥ 2`) is an orthonormal family with all members of equal degree `d ≠ 0`,
whose differences `χⱼ − χ₀` are supported in `A` (`1 ∉ A`), and `X : Fin n → CF(G)` is an
orthonormal
family in the target with `τ (χⱼ − χ₀) = Xⱼ − X₀` (the (1.4) signed-difference image equation), then
`{χ₀, …, χₙ₋₁} = range χ` is coherent, with extension `ν φ = ∑ⱼ ⟨φ, χⱼ⟩ • Xⱼ` (`coherentImageMap`).

This is the seed for both the equal-minimal-degree base prefix of (6.6) and the set `Y = S(H')` of
(6.8), where coherence holds *directly* by (1.1)+(1.4) (the (5.6) degree induction is unavailable at
equal degree).  The construction needs no `τ₁`-residual: on the lattice `ℤ[range χ]` the residual
vanishes, so `extension_inner_eq` is pure Parseval (`coherentImageMap_inner_eq`) and `τ` enters only
through `extends_on_supported`, where `ℤ[range χ, A]` is generated by the differences `χⱼ − χ₀`
(`zSupportedSpan_range_subset_span_sub_zero`), on which `ν` and `τ` agree by `himg`. -/
noncomputable def coherentEqualDegree
    {τ : IntegralCharacterMap L G} {A : Set L} {n : ℕ} [NeZero n]
    {χ : Fin n → ClassFunction L ℂ} {X : Fin n → ClassFunction G ℂ}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hn : 2 ≤ n)
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    (horthX : ∀ i j, ClassFunction.inner (X i) (X j) = if i = j then (1 : ℂ) else 0)
    (himg : ∀ j, τ (χ j - χ 0) = X j - X 0)
    (hXZ : ∀ j, X j ∈ ZIrr G)
    (hdeg : ∀ j, ((χ j : ClassFunction L ℂ) : L → ℂ) 1 = ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ j, (χ j - χ 0).support ⊆ A) :
    IsCoherent τ (Set.range χ) A := by
  classical
  have h1n : 1 < n := by omega
  have hi1 : (⟨1, h1n⟩ : Fin n) ≠ 0 := by
    intro h; exact absurd (congrArg Fin.val h) (by simp)
  refine ⟨⟨χ ⟨1, h1n⟩ - χ 0,
      ⟨Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self _))
        (Submodule.subset_span (Set.mem_range_self _)), hsuppdiff ⟨1, h1n⟩⟩, ?_⟩,
    coherentImageMap (L := L) (G := G) χ X, ?_, ?_, ?_⟩
  · -- nonzero: `χ₁ − χ₀ ≠ 0` from orthonormality.
    rw [sub_ne_zero]
    intro h
    have hcontra : (0 : ℂ) = 1 :=
      calc (0 : ℂ) = ClassFunction.inner (χ (⟨1, h1n⟩ : Fin n)) (χ 0) := by
            rw [horthχ, if_neg hi1]
        _ = ClassFunction.inner (χ 0) (χ 0) := by rw [h]
        _ = 1 := by rw [horthχ, if_pos rfl]
    exact zero_ne_one hcontra
  · -- extension_inner_eq: pure Parseval on `ℤ[range χ]`.
    intro φ ψ hφ hψ
    exact coherentImageMap_inner_eq horthχ horthX hφ hψ
  · -- extends_on_supported: agreement on the difference generators of `ℤ[range χ, A]`.
    intro φ hφ
    refine eq_on_zSpan_of_eq_on (T := Set.range (fun j => χ j - χ 0)) ?_
      (zSupportedSpan_range_subset_span_sub_zero hdeg hdeg0 h1A hφ)
    rintro x ⟨j, rfl⟩
    rw [map_sub, coherentImageMap_apply_eq horthχ j, coherentImageMap_apply_eq horthχ 0, himg j]
  · -- extension_mem_ZIrr: each member maps to `Xⱼ ∈ ℤ[Irr G]` (`coherentImageMap_apply_eq`), so
    -- `ℤ[range χ]` maps into `ℤ[Irr G]`.
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        rw [coherentImageMap_apply_eq horthχ j]; exact hXZ j
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul c y _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ c ih

open IntegralCharacterMap in
/-- **Peterfalvi (5.7) core: an equal-degree set with *arbitrary* member norms is coherent.**

The weighted form of `coherentEqualDegree`.  Hypothesis (5.2) gives the members of `𝒮` only
*pairwise orthogonality* — a reducible member has `‖χ‖² > 1` — so the book's (5.7) may not assume
unit norm, and neither does this builder (issue 0157).

Inputs: `χ : Fin n → CF(L)` (`n ≥ 2`) pairwise orthogonal with nonzero norms, all of equal degree
`d ≠ 0`, differences supported in `A` (`1 ∉ A`); and a target family `X : Fin n → CF(G)` of virtual
characters matching the **Gram matrix** of `χ` (`⟨Xᵢ, Xⱼ⟩ = ⟨χᵢ, χⱼ⟩` — the orthonormal builder's
`horthX` is the `⟨χᵢ, χⱼ⟩ = δᵢⱼ` case), with `τ (χⱼ − χ₀) = Xⱼ − X₀`.

The extension is the **norm-rescaled** reconstruction `ν φ = ∑ⱼ ⟨φ, χⱼ⟩ · ‖χⱼ‖⁻² • Xⱼ`, which
sends `χₖ ↦ Xₖ` (`coherentImageMap_apply_eq_of_orthogonal`) and is an isometry on `ℤ[range χ]` by
weighted Parseval (`coherentImageMapW_inner_eq`).  `IsCoherent` asks for an isometry, not for
orthonormal images, so nothing else changes.

`coherentEqualDegree` is kept as the unit-norm construction because its `extension` is
`coherentImageMap χ X` *definitionally* (`coherentEqualDegree_extension`), an API several
downstream consumers rely on; here the extension carries the `‖χⱼ‖⁻²` rescaling. -/
noncomputable def coherentEqualDegreeW
    {τ : IntegralCharacterMap L G} {A : Set L} {n : ℕ} [NeZero n]
    {χ : Fin n → ClassFunction L ℂ} {X : Fin n → ClassFunction G ℂ}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hn : 2 ≤ n)
    (horthχ : ∀ i j, i ≠ j → ClassFunction.inner (χ i) (χ j) = 0)
    (hnorm : ∀ j, ClassFunction.inner (χ j) (χ j) ≠ 0)
    (hgram : ∀ i j, ClassFunction.inner (X i) (X j) = ClassFunction.inner (χ i) (χ j))
    (himg : ∀ j, τ (χ j - χ 0) = X j - X 0)
    (hXZ : ∀ j, X j ∈ ZIrr G)
    (hdeg : ∀ j, ((χ j : ClassFunction L ℂ) : L → ℂ) 1 = ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ j, (χ j - χ 0).support ⊆ A) :
    IsCoherent τ (Set.range χ) A := by
  classical
  have h1n : 1 < n := by omega
  have hi1 : (⟨1, h1n⟩ : Fin n) ≠ 0 := by
    intro h; exact absurd (congrArg Fin.val h) (by simp)
  refine ⟨⟨χ ⟨1, h1n⟩ - χ 0,
      ⟨Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self _))
        (Submodule.subset_span (Set.mem_range_self _)), hsuppdiff ⟨1, h1n⟩⟩, ?_⟩,
    coherentImageMap (L := L) (G := G) χ
      (fun j => (ClassFunction.inner (χ j) (χ j))⁻¹ • X j), ?_, ?_, ?_⟩
  · -- nonzero: `χ₁ = χ₀` would make the nonzero norm `⟨χ₀, χ₀⟩` an off-diagonal `0`.
    rw [sub_ne_zero]
    intro h
    have hoff := horthχ ⟨1, h1n⟩ 0 hi1
    rw [h] at hoff
    exact hnorm 0 hoff
  · -- extension_inner_eq: weighted Parseval on `ℤ[range χ]`.
    intro φ ψ hφ hψ
    exact coherentImageMapW_inner_eq horthχ hnorm hgram hφ hψ
  · -- extends_on_supported: agreement on the difference generators of `ℤ[range χ, A]`.
    intro φ hφ
    refine eq_on_zSpan_of_eq_on (T := Set.range (fun j => χ j - χ 0)) ?_
      (zSupportedSpan_range_subset_span_sub_zero hdeg hdeg0 h1A hφ)
    rintro x ⟨j, rfl⟩
    rw [map_sub, coherentImageMap_apply_eq_of_orthogonal horthχ hnorm j,
      coherentImageMap_apply_eq_of_orthogonal horthχ hnorm 0, himg j]
  · -- extension_mem_ZIrr: each member maps to `Xⱼ ∈ ℤ[Irr G]`.
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        rw [coherentImageMap_apply_eq_of_orthogonal horthχ hnorm j]; exact hXZ j
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul c y _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ c ih

open IntegralCharacterMap in
/-- The `extension` field of `coherentEqualDegree` is the Fourier image map `coherentImageMap χ X`.
-/
theorem coherentEqualDegree_extension
    {τ : IntegralCharacterMap L G} {A : Set L} {n : ℕ} [NeZero n]
    {χ : Fin n → ClassFunction L ℂ} {X : Fin n → ClassFunction G ℂ}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hn : 2 ≤ n)
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    (horthX : ∀ i j, ClassFunction.inner (X i) (X j) = if i = j then (1 : ℂ) else 0)
    (himg : ∀ j, τ (χ j - χ 0) = X j - X 0)
    (hXZ : ∀ j, X j ∈ ZIrr G)
    (hdeg : ∀ j, ((χ j : ClassFunction L ℂ) : L → ℂ) 1 = ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ((χ 0 : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ j, (χ j - χ 0).support ⊆ A) :
    (coherentEqualDegree hn horthχ horthX himg hXZ hdeg hdeg0 h1A hsuppdiff).extension
      = coherentImageMap (L := L) (G := G) χ X := rfl

/-- Transport the `extension` of a coherence witness across an equality of the coherent set: the
`extension` field is set-independent data, so it is unchanged by `▸`-rewriting the set. -/
theorem IsCoherent.extension_eqRec {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ S₂ : Set (ClassFunction L ℂ)} (h : S₁ = S₂) (c : IsCoherent τ S₁ A) :
    (h ▸ c).extension = c.extension := by subst h; rfl

open scoped Classical in
open IntegralCharacterMap in
/-- **Sign-swap relabel of a coherence witness on a 2-element equal-degree set** (Peterfalvi (6.8.1)
relabel, mmd 04.8 L176: "replacing `η₁^{τ₁}, η₂^{τ₁}` by `-η₂^{τ₁}, -η₁^{τ₁}`", and the `X`-analogue
for `n = 2`).

Given a coherence witness `c` for the orthonormal equal-degree pair `{φ₀, φ₁}` (`φ₀ ≠ φ₁`,
`φ₁(1) = φ₀(1) ≠ 0`, difference supported in `A`, `1 ∉ A`), there is a second coherence witness `c'`
for the *same set* whose extension sends `φ₀ ↦ -c.extension φ₁` and `φ₁ ↦ -c.extension φ₀` — the
"swap-and-negate" of the two images.  The swapped images `-c.extension φ₁, -c.extension φ₀` are
still orthonormal and in `ℤ[Irr G]` (signs square out), and the supported difference is preserved:
`φ₁ - φ₀ ↦ (-c.extension φ₀) - (-c.extension φ₁) = c.extension φ₁ - c.extension φ₀ = τ(φ₁ - φ₀)`,
which is *exactly* why `extends_on_supported` survives the swap (it would fail for an unequal-degree
pair, where the supported lattice is generated by a degree-ratio difference instead).  Built via
`coherentEqualDegree` with source `![φ₀, φ₁]` and target `![-c.extension φ₁, -c.extension φ₀]`. -/
theorem coherentEqualDegree_swap_neg
    {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {φ₀ φ₁ : ClassFunction L ℂ}
    (c : IsCoherent τ ({φ₀, φ₁} : Set (ClassFunction L ℂ)) A)
    (horth : ClassFunction.inner φ₀ φ₁ = 0)
    (hn0 : ClassFunction.inner φ₀ φ₀ = 1) (hn1 : ClassFunction.inner φ₁ φ₁ = 1)
    (hdeg : (φ₁ : L → ℂ) 1 = (φ₀ : L → ℂ) 1) (hdeg0 : (φ₀ : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A) (hsupp : (φ₁ - φ₀).support ⊆ A) :
    ∃ c' : IsCoherent τ ({φ₀, φ₁} : Set (ClassFunction L ℂ)) A,
      c'.extension φ₀ = -c.extension φ₁ ∧ c'.extension φ₁ = -c.extension φ₀ := by
  classical
  -- membership in `{φ₀, φ₁}` and its `ℤ`-span.
  have hmem0 : φ₀ ∈ ({φ₀, φ₁} : Set (ClassFunction L ℂ)) := Set.mem_insert _ _
  have hmem1 : φ₁ ∈ ({φ₀, φ₁} : Set (ClassFunction L ℂ)) := Set.mem_insert_of_mem _ rfl
  have hsp0 : φ₀ ∈ zSpan (L := L) ({φ₀, φ₁} : Set _) := Submodule.subset_span hmem0
  have hsp1 : φ₁ ∈ zSpan (L := L) ({φ₀, φ₁} : Set _) := Submodule.subset_span hmem1
  -- target images are orthonormal (from `c.extension_inner_eq` + source orthonormality).
  have hψ00 : ClassFunction.inner (c.extension φ₀) (c.extension φ₀) = 1 := by
    rw [c.extension_inner_eq φ₀ φ₀ hsp0 hsp0, hn0]
  have hψ11 : ClassFunction.inner (c.extension φ₁) (c.extension φ₁) = 1 := by
    rw [c.extension_inner_eq φ₁ φ₁ hsp1 hsp1, hn1]
  have hψ01 : ClassFunction.inner (c.extension φ₀) (c.extension φ₁) = 0 := by
    rw [c.extension_inner_eq φ₀ φ₁ hsp0 hsp1, horth]
  have hψ10 : ClassFunction.inner (c.extension φ₁) (c.extension φ₀) = 0 := by
    rw [c.extension_inner_eq φ₁ φ₀ hsp1 hsp0,
      OddOrder.RepresentationTheory.inner_conj_symm φ₀ φ₁, horth, star_zero]
  -- ZIrr membership of the target images.
  have hZ0 : c.extension φ₀ ∈ ZIrr G := c.extension_mem_ZIrr φ₀ hsp0
  have hZ1 : c.extension φ₁ ∈ ZIrr G := c.extension_mem_ZIrr φ₁ hsp1
  -- `coherentEqualDegree` inputs for `χ = ![φ₀, φ₁]`, `X = ![-c.extension φ₁, -c.extension φ₀]`.
  have horthχ : ∀ i j : Fin 2, ClassFunction.inner ((![φ₀, φ₁] : Fin 2 → _) i)
      ((![φ₀, φ₁] : Fin 2 → _) j) = if i = j then (1 : ℂ) else 0 := by
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · simpa using hn0
    · simpa using horth
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
        Fin.reduceEq, ↓reduceIte]
      rw [OddOrder.RepresentationTheory.inner_conj_symm φ₀ φ₁, horth, star_zero]
    · simpa using hn1
  have horthX : ∀ i j : Fin 2,
      ClassFunction.inner ((![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _) i)
      ((![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _) j) = if i = j then (1 : ℂ) else 0 := by
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
        Fin.reduceEq, ↓reduceIte, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
        neg_neg]
    · exact hψ11
    · exact hψ10
    · exact hψ01
    · exact hψ00
  have himg : ∀ j : Fin 2, τ ((![φ₀, φ₁] : Fin 2 → _) j - (![φ₀, φ₁] : Fin 2 → _) 0)
      = (![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _) j
        - (![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _) 0 := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simp
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
      have hsuppmem : (φ₁ - φ₀) ∈ zSupportedSpan (L := L) ({φ₀, φ₁} : Set _) A :=
        ⟨Submodule.sub_mem _ hsp1 hsp0, hsupp⟩
      have hext := c.extends_on_supported (φ₁ - φ₀) hsuppmem
      rw [map_sub] at hext
      rw [← hext, neg_sub_neg]
  have hXZ : ∀ j : Fin 2, (![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _) j ∈ ZIrr G := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simpa using Submodule.neg_mem _ hZ1
    · simpa using Submodule.neg_mem _ hZ0
  have hdeg' : ∀ j : Fin 2, (((![φ₀, φ₁] : Fin 2 → _) j : ClassFunction L ℂ) : L → ℂ) 1
      = (((![φ₀, φ₁] : Fin 2 → _) 0 : ClassFunction L ℂ) : L → ℂ) 1 := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rfl
    · simpa using hdeg
  have hdeg0' : (((![φ₀, φ₁] : Fin 2 → _) 0 : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0 := by
    simpa using hdeg0
  have hsuppdiff : ∀ j : Fin 2,
      ((![φ₀, φ₁] : Fin 2 → _) j - (![φ₀, φ₁] : Fin 2 → _) 0).support ⊆ A := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simp
    · simpa using hsupp
  -- the swapped witness over `range ![φ₀,φ₁]`, transported to `{φ₀,φ₁}`.
  have hr : Set.range (![φ₀, φ₁] : Fin 2 → ClassFunction L ℂ) = ({φ₀, φ₁} : Set _) := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  refine ⟨hr ▸ coherentEqualDegree (by norm_num : (2 : ℕ) ≤ 2) horthχ horthX himg hXZ hdeg'
      hdeg0' h1A hsuppdiff, ?_, ?_⟩
  · rw [IsCoherent.extension_eqRec hr, coherentEqualDegree_extension]
    have h0 := coherentImageMap_apply_eq (L := L) (G := G)
      (χ := (![φ₀, φ₁] : Fin 2 → _)) (X := (![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _))
      horthχ 0
    simpa using h0
  · rw [IsCoherent.extension_eqRec hr, coherentEqualDegree_extension]
    have h1 := coherentImageMap_apply_eq (L := L) (G := G)
      (χ := (![φ₀, φ₁] : Fin 2 → _)) (X := (![-c.extension φ₁, -c.extension φ₀] : Fin 2 → _))
      horthχ 1
    simpa using h1

open OddOrder.RepresentationTheory in
/-- **Per-member (5.5)+(5.2.e) orthogonality `χ'^{τ₁} ⊥ R(χ)`.**  For a family member `χ' ∈ S₁`
with its `ψ = 0` decomposition `D'` (so `χ'^{τ₁'} = D'.X ∈ ℤ[R(χ')]` by (5.5),
`eq_sum_of_psi_eq_zero`), whose image family `R(χ')` is orthogonal to the distinguished `R(χ) :=
R₀` (the (5.2.e) input `D'.imageFamily.Orthogonal R₀`), and whose auxiliary isometry agrees with the
running extension at `χ'` (`htau1 : D'.tau1 χ' = hS₁.extension χ'`), the running image
`χ'^{τ₁} = hS₁.extension χ'` is orthogonal to every `α ∈ R(χ)`:
`⟨hS₁.extension χ', α⟩ = ⟨D'.tau1 χ', α⟩ = ⟨D'.X, α⟩ = 0`.  This is the per-character content of
mmd L77, the building block of `hperElem`. -/
theorem inner_extension_member_orthogonal_imageSet
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A)
    {χ χ' : ClassFunction L ℂ}
    (R₀ : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (D' : CharacterPsiDecomposition (L := L) (G := G) τ χ' 0)
    (hortho : D'.imageFamily.Orthogonal R₀)
    (htau1 : D'.tau1 χ' = hS₁.extension χ')
    {α : ClassFunction G ℂ} (hα : α ∈ R₀.imageSet) :
    ClassFunction.inner (hS₁.extension χ') α = 0 := by
  rw [← htau1, (D'.eq_sum_of_psi_eq_zero).2.1,
    D'.inner_X_orthogonal_imageSet_of_orthogonal R₀ hortho hα]

end OddOrder.Peterfalvi.S07


