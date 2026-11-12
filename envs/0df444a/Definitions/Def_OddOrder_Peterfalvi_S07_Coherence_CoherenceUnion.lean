-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion
-- name    : OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:59:08.49576+00:00
-- url     : https://prove2.me/theorems/966344c1-48f7-4324-a39b-10c955aaf951
-- title:
--   Peterfalvi (5.6.2)–(5.6.3), (6.8): coherence-union extension, orthogonal coherent union, (6.6) $X$ coherence
-- statement:
--   Part of the coherence development of Peterfalvi §7: the coherence-union extension $\tau_2$, the orthogonal coherent union, the diagonal-aware union for (6.8), and the coherence of the (6.6) set $X$ by repeated use of (5.6).
--
--   Main definitions: `coherentUnion_of_glued_withDiagonal` (Peterfalvi (6.8.1): diagonal-aware coherence of the union $X\cup Y$) and its generator-level form, `pairSet` (the pair $\{\chi_i,\bar\chi_i\}$), `pairUnion` (the base set $S_0$ with the pairs for $j<i$), `coherentPairChain` (Peterfalvi (6.6): the iteration engine for repeated use of (5.6)) and `coherentOfPairChainCover` (Peterfalvi (6.6): coherence of $X=S-S(Z)$).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_Coherence/CoherenceUnion.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_Coherence/CoherenceUnion.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceExtensionTau2

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

/-- **Two-lattice orthogonal block identity.**

For `a, a' ∈ ℤ[X]` and `b, b' ∈ ℤ[Y]`, if `νX` preserves `⟨·,·⟩` on `ℤ[X]`, `νY` preserves it on
`ℤ[Y]`, the source lattices are orthogonal (`⟨a, b'⟩ = ⟨b, a'⟩ = 0`), and the images are orthogonal
(`⟨νX a, νY b'⟩ = ⟨νY b, νX a'⟩ = 0`), then
`⟨νX a + νY b, νX a' + νY b'⟩ = ⟨a + b, a' + b'⟩`.

Both sides expand to `⟨a, a'⟩ + ⟨b, b'⟩` by the respective orthogonalities; the diagonal blocks
match via the lattice isometries `hνX`, `hνY`.  This is the algebraic heart of the (6.8.1)/(6.8.2)
`τ₃` gluing. -/
theorem inner_orthogonal_glued_eq
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {νX νY : IntegralCharacterMap L G} {X Y : Set (ClassFunction L ℂ)}
    (hνX : ∀ u v : ClassFunction L ℂ, u ∈ Submodule.span ℤ X → v ∈ Submodule.span ℤ X →
      ClassFunction.inner (νX u) (νX v) = ClassFunction.inner u v)
    (hνY : ∀ u v : ClassFunction L ℂ, u ∈ Submodule.span ℤ Y → v ∈ Submodule.span ℤ Y →
      ClassFunction.inner (νY u) (νY v) = ClassFunction.inner u v)
    (hsrc_ortho : ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner u v = 0)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner (νX u) (νY v) = 0)
    {a a' b b' : ClassFunction L ℂ}
    (ha : a ∈ Submodule.span ℤ X) (ha' : a' ∈ Submodule.span ℤ X)
    (hb : b ∈ Submodule.span ℤ Y) (hb' : b' ∈ Submodule.span ℤ Y) :
    ClassFunction.inner (νX a + νY b) (νX a' + νY b') =
      ClassFunction.inner (a + b) (a' + b') := by
  -- Source-side orthogonalities (both directions, via conjugate symmetry).
  have hab' : ClassFunction.inner a b' = 0 := hsrc_ortho a ha b' hb'
  have hba' : ClassFunction.inner b a' = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hsrc_ortho a' ha' b hb, star_zero]
  -- Image-side orthogonalities (both directions, via conjugate symmetry).
  have hXaYb' : ClassFunction.inner (νX a) (νY b') = 0 := himg_ortho a ha b' hb'
  have hYbXa' : ClassFunction.inner (νY b) (νX a') = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, himg_ortho a' ha' b hb, star_zero]
  rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_add_right, ClassFunction.inner_add_left,
    ClassFunction.inner_add_right, ClassFunction.inner_add_right,
    hXaYb', hYbXa', hab', hba', hνX a a' ha ha', hνY b b' hb hb']

/-- **Inner-product preservation on `Z[X ∪ Y]` for an orthogonal coherent union.**

If a map `ν` agrees with `νX` on `ℤ[X]` and with `νY` on `ℤ[Y]`, and the four orthogonal-block
hypotheses of `inner_orthogonal_glued_eq` hold, then `ν` preserves `⟨·,·⟩` on the whole lattice
`ℤ[X ∪ Y]`.  Every `φ ∈ ℤ[X ∪ Y] = ℤ[X] ⊔ ℤ[Y]` (`Submodule.span_union`) splits as `a + b` with
`a ∈ ℤ[X]`, `b ∈ ℤ[Y]`, so `ν φ = νX a + νY b`; the identity then closes by
`inner_orthogonal_glued_eq`.  This is precisely the weakened `IsCoherent.extension_inner_eq`
obligation for the glued map `τ₃` of (6.8.1)/(6.8.2). -/
theorem inner_eq_on_zSpan_union_of_orthogonal
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {ν νX νY : IntegralCharacterMap L G} {X Y : Set (ClassFunction L ℂ)}
    (hagreeX : ∀ u ∈ Submodule.span ℤ X, ν u = νX u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ Y, ν v = νY v)
    (hνX : ∀ u v : ClassFunction L ℂ, u ∈ Submodule.span ℤ X → v ∈ Submodule.span ℤ X →
      ClassFunction.inner (νX u) (νX v) = ClassFunction.inner u v)
    (hνY : ∀ u v : ClassFunction L ℂ, u ∈ Submodule.span ℤ Y → v ∈ Submodule.span ℤ Y →
      ClassFunction.inner (νY u) (νY v) = ClassFunction.inner u v)
    (hsrc_ortho : ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner u v = 0)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner (νX u) (νY v) = 0)
    {φ ψ : ClassFunction L ℂ}
    (hφ : φ ∈ Submodule.span ℤ (X ∪ Y)) (hψ : ψ ∈ Submodule.span ℤ (X ∪ Y)) :
    ClassFunction.inner (ν φ) (ν ψ) = ClassFunction.inner φ ψ := by
  -- Decompose `φ, ψ ∈ ℤ[X ∪ Y] = ℤ[X] ⊔ ℤ[Y]`.
  rw [Submodule.span_union, Submodule.mem_sup] at hφ hψ
  obtain ⟨a, ha, b, hb, hφeq⟩ := hφ
  obtain ⟨a', ha', b', hb', hψeq⟩ := hψ
  -- `ν φ = νX a + νY b`, `ν ψ = νX a' + νY b'`.
  have hνφ : ν φ = νX a + νY b := by
    rw [← hφeq, map_add, hagreeX a ha, hagreeY b hb]
  have hνψ : ν ψ = νX a' + νY b' := by
    rw [← hψeq, map_add, hagreeX a' ha', hagreeY b' hb']
  rw [hνφ, hνψ, ← hφeq, ← hψeq]
  exact inner_orthogonal_glued_eq hνX hνY hsrc_ortho himg_ortho ha ha' hb hb'

/-- Image-side orthogonality follows from a glued map that agrees with the two pieces and
preserves mixed inner products. -/
theorem image_orthogonal_of_mixed_inner_eq
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {ν νX νY : IntegralCharacterMap L G} {X Y : Set (ClassFunction L ℂ)}
    (hagreeX : ∀ u ∈ Submodule.span ℤ X, ν u = νX u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ Y, ν v = νY v)
    (hmixed : ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner (ν u) (ν v) = ClassFunction.inner u v)
    (hsrc_ortho : ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner u v = 0) :
    ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner (νX u) (νY v) = 0 := by
  intro u hu v hv
  rw [← hagreeX u hu, ← hagreeY v hv, hmixed u hu v hv, hsrc_ortho u hu v hv]

/-- A mixed inner-product equality checked on generators extends to their integral spans. -/
theorem mixed_inner_eq_on_zSpan_of_eq_on
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {ν : IntegralCharacterMap L G} {X Y : Set (ClassFunction L ℂ)}
    (hmixed : ∀ x ∈ X, ∀ y ∈ Y,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y) :
    ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner (ν u) (ν v) = ClassFunction.inner u v := by
  have hright : ∀ x ∈ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner (ν x) (ν v) = ClassFunction.inner x v := by
    intro x hx v hv
    induction hv using Submodule.span_induction with
    | mem y hy => exact hmixed x hx y hy
    | zero =>
        rw [map_zero, ClassFunction.inner_zero_right, ClassFunction.inner_zero_right]
    | add y z _ _ ihy ihz =>
        rw [map_add, ClassFunction.inner_add_right, ClassFunction.inner_add_right, ihy, ihz]
    | smul a y _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ a (ν y),
          ← Int.cast_smul_eq_zsmul ℂ a y,
          OddOrder.RepresentationTheory.inner_smul_right,
          OddOrder.RepresentationTheory.inner_smul_right, ih]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
      intro v hv
      exact hright x hx v hv
  | zero =>
      intro v _hv
      rw [map_zero, ClassFunction.inner_zero_left, ClassFunction.inner_zero_left]
  | add x y _ _ ihx ihy =>
      intro v hv
      rw [map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left, ihx v hv, ihy v hv]
  | smul a x _ ih =>
      intro v hv
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ a (ν x),
        ← Int.cast_smul_eq_zsmul ℂ a x,
        ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, ih v hv]

/-- **Peterfalvi (6.8.1) diagonal-aware coherence of the union `X ∪ Y`.**

The plain `coherentUnion_of_glued` requires the generation hypothesis

`zSupportedSpan (X ∪ Y) A ⊆ ℤ[ zSupportedSpan X A ∪ zSupportedSpan Y A ]`,

which is **false** in the (6.8.1) situation.  With `χ₁ ∈ X` the minimal-degree anchor
(`χ₁(1) = a·|W₁|`, `a > 1`) and `η₁ ∈ Y` (`η₁(1) = |W₁|`), the *cross-diagonal* `χ₁ − a·η₁` is
supported (vanishes at `1`) and lies in `ℤ[X ∪ Y]`, yet **not** in the right-hand `ℤ`-span: a
supported `X`-combination `∑cᵢχᵢ` has degree `0` (so `∑cᵢdᵢ = 0`), a supported `Y`-combination
`∑eⱼηⱼ` has degree `0` (so `∑eⱼ = 0`), and by linear independence of the disjoint irreducibles
`χ₁ − a·η₁` would force its `X`-part `χ₁` to be supported — but `χ₁(1) ≠ 0`.  (Degree count: a
supported `∑cᵢχᵢ + ∑eⱼηⱼ` has `∑eⱼ = −a∑cᵢdᵢ`, and splits as `X`-supported `+` `Y`-supported only
when `∑cᵢdᵢ = 0`; `χ₁ − a·η₁` has `∑cᵢdᵢ = d₁ = 1`.)  See
`notes/peterfalvi/s08_6_8_blocker_central_Z.md` (framing correction #2).

The fix threads a set `D` of supported cross-diagonals on which the glued map `ν` is **already
known** to agree with the base map `τ` (`hDτ` — the (6.8.1) `b ≡ 0` conclusion, i.e.
`(χ₁ − a·η₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}`), and enlarges the generating set with `D`.  With the single
cross-diagonal `χ₁ − a·η₁` adjoined, the generation hypothesis `hgen` *is* satisfiable:
`zSupportedSpan (X ∪ Y) A = ℤ[ {χᵢ − dᵢχ₁} ∪ {ηⱼ − η₁} ∪ {χ₁ − a·η₁} ]`, the degree-`0` sublattice
of `ℤ[X ∪ Y]` (rank `|X| + |Y| − 1`).

The `extension_inner_eq` (isometry) and `extension_mem_ZIrr` obligations are **unchanged** from
`coherentUnion_of_glued`: they live on `ℤ[X ∪ Y]` and never see `D`.  Only `extends_on_supported`
gains the `D`-generators, discharged directly by `hDτ`.  Taking `D = ∅` recovers
`coherentUnion_of_glued`. -/
noncomputable def coherentUnion_of_glued_withDiagonal
    {τ : IntegralCharacterMap L G} {X Y : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hX : IsCoherent τ X A) (hY : IsCoherent τ Y A)
    (ν : IntegralCharacterMap L G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ X, ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ Y, ν v = hY.extension v)
    (hsrc_ortho : ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner u v = 0)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner (hX.extension u) (hY.extension v) = 0)
    (D : Set (ClassFunction L ℂ))
    (hDτ : ∀ d ∈ D, ν d = τ d)
    (hgen : zSupportedSpan (L := L) (X ∪ Y) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) X A ∪ zSupportedSpan (L := L) Y A ∪ D)) :
    IsCoherent τ (X ∪ Y) A := by
  classical
  refine ⟨?_, ν, ?_, ?_, ?_⟩
  · -- nonzero: inherited from `X ⊆ X ∪ Y`.
    obtain ⟨φ, hφmem, hφne⟩ := hX.nonzero
    exact ⟨φ, zSupportedSpan_mono_left Set.subset_union_left hφmem, hφne⟩
  · -- `extension_inner_eq` on `ℤ[X ∪ Y]` via the two-lattice gluing identity (`D`-independent).
    intro φ ψ hφ hψ
    exact inner_eq_on_zSpan_union_of_orthogonal hagreeX hagreeY
      hX.extension_inner_eq hY.extension_inner_eq hsrc_ortho himg_ortho hφ hψ
  · -- `extends_on_supported`: `ν = τ` on the generator `Z[X,A] ∪ Z[Y,A] ∪ D`, then
    -- `span_induction`.
    intro φ hφ
    have hagree_T : ∀ y ∈ zSupportedSpan (L := L) X A ∪ zSupportedSpan (L := L) Y A ∪ D,
        ν y = τ y := by
      intro y hy
      rcases hy with (hyX | hyY) | hyD
      · rw [hagreeX y hyX.1, hX.extends_on_supported y hyX]
      · rw [hagreeY y hyY.1, hY.extends_on_supported y hyY]
      · exact hDτ y hyD
    exact IntegralCharacterMap.eq_on_zSpan_of_eq_on hagree_T (hgen hφ)
  · -- extension_mem_ZIrr: each generator of `ℤ[X ∪ Y]` maps via `νX`/`νY` into `ℤ[Irr G]`
    -- (`D`-independent).
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hyX | hyY
        · rw [hagreeX y (Submodule.subset_span hyX)]
          exact hX.extension_mem_ZIrr y (Submodule.subset_span hyX)
        · rw [hagreeY y (Submodule.subset_span hyY)]
          exact hY.extension_mem_ZIrr y (Submodule.subset_span hyY)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul c y _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ c ih

/-- Generator-level form of `coherentUnion_of_glued_withDiagonal` (the diagonal-aware analogue of
`coherentUnion_of_glued_of_generator_mixed_inner_eq`).

The caller checks agreement (`hagreeX`/`hagreeY`) and mixed inner products (`hmixed`) only on the
two generating families `X`, `Y`; the span obligations and `himg_ortho` are derived
(`eq_on_zSpan_of_eq_on`, `mixed_inner_eq_on_zSpan_of_eq_on`, `image_orthogonal_of_mixed_inner_eq`).
The extra `D`/`hDτ` thread the supported cross-diagonals on which `ν = τ` is already known (the
(6.8.1) `b ≡ 0` conclusion), enlarging the generation hypothesis `hgen` to the satisfiable form. -/
noncomputable def coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    {τ : IntegralCharacterMap L G} {X Y : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hX : IsCoherent τ X A) (hY : IsCoherent τ Y A)
    (ν : IntegralCharacterMap L G)
    (hagreeX : ∀ x ∈ X, ν x = hX.extension x)
    (hagreeY : ∀ y ∈ Y, ν y = hY.extension y)
    (hsrc_ortho : ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner u v = 0)
    (hmixed : ∀ x ∈ X, ∀ y ∈ Y,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction L ℂ))
    (hDτ : ∀ d ∈ D, ν d = τ d)
    (hgen : zSupportedSpan (L := L) (X ∪ Y) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) X A ∪ zSupportedSpan (L := L) Y A ∪ D)) :
    IsCoherent τ (X ∪ Y) A :=
  coherentUnion_of_glued_withDiagonal hX hY ν
    (fun _ hu => IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeX hu)
    (fun _ hv => IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeY hv)
    hsrc_ortho
    (image_orthogonal_of_mixed_inner_eq
      (fun _ hu => IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeX hu)
      (fun _ hv => IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeY hv)
      (mixed_inner_eq_on_zSpan_of_eq_on hmixed) hsrc_ortho)
    D hDτ hgen

/-- **Peterfalvi (6.6): "Set `X = {χ₁,…,χₙ}` where `χ₁(1) ≤ ⋯ ≤ χₙ(1)`".**

The (6.6) proof opens by *sorting* the finite set `X = S − S(Z)` by character degree: it writes
`X = {χ₁,…,χₙ}` with `χ₁(1) ≤ ⋯ ≤ χₙ(1)`.  Formally this is a monotone enumeration of the finite
set: an injective surjection `e : Fin n → X` (here `n = |X| = X.ncard`) along which the real degree
key `χ ↦ (characterDegree χ).re` is non-decreasing.

The construction is the standard one: pick any bijection `Fin n ≃ X` (from finiteness), then permute
the index set by `Tuple.sort` applied to the degree key, which makes the composite degree-monotone
(`Tuple.monotone_sort`).  Nothing here uses irreducibility, the induced-from-`K` structure, or the
`p`-power degree facts — it is the purely order-theoretic "sort a finite family by a real key" step,
stated for an arbitrary finite set of class functions.  The enumeration is the indexing `χ₁,…,χₙ`
the rest of the (6.6) argument refers to; the degree of `χᵢ` (a positive integer for genuine
characters) is recorded through its real part, which the monotonicity orders. -/
theorem exists_monotoneDegreeEnum {X : Set (ClassFunction L ℂ)} (hXfin : X.Finite) :
    ∃ e : Fin X.ncard → ClassFunction L ℂ,
      Function.Injective e ∧ (∀ i, e i ∈ X) ∧ (∀ χ ∈ X, ∃ i, e i = χ) ∧
      ∀ ⦃i j : Fin X.ncard⦄, i ≤ j →
        (OddOrder.Peterfalvi.S03.characterDegree (e i)).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (e j)).re := by
  classical
  let : Fintype X := hXfin.fintype
  -- `Fin n ≃ X`, where `n = X.ncard`.
  have hcard : Fintype.card X = X.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  let g : X ≃ Fin X.ncard := Fintype.equivFinOfCardEq hcard
  -- The real degree key, pulled back along the chosen indexing.
  let k : Fin X.ncard → ℝ :=
    fun i => (OddOrder.Peterfalvi.S03.characterDegree (g.symm i : ClassFunction L ℂ)).re
  -- Sort the index set by the key; the composite key is monotone.
  let σ : Equiv.Perm (Fin X.ncard) := Tuple.sort k
  refine ⟨fun i => (g.symm (σ i) : ClassFunction L ℂ), ?_, ?_, ?_, ?_⟩
  · -- Injective: `Subtype.val ∘ g.symm ∘ σ`, all three injective.
    intro i j hij
    exact σ.injective (g.symm.injective (Subtype.coe_injective hij))
  · -- Each value lies in `X`.
    intro i
    exact (g.symm (σ i)).2
  · -- Surjective onto `X`: hit `χ` at `i = σ⁻¹ (g ⟨χ, _⟩)`.
    intro χ hχ
    refine ⟨σ.symm (g ⟨χ, hχ⟩), ?_⟩
    simp only [σ.apply_symm_apply, g.symm_apply_apply]
  · -- Monotone in the key: `(characterDegree (e ·)).re = (k ∘ σ) ·`, and `k ∘ σ` is monotone.
    intro i j hij
    exact Tuple.monotone_sort k hij

/-- **Peterfalvi (6.6): "By (1.1), `n ≥ 2`".**

The opening step of the (6.6) proof: with `X = S − S(Z)` the set of irreducible characters of
`L` not killing `Z`, one has `n := |X| ≥ 2`.  The textbook justification "By (1.1)" unpacks as
follows.  Every `χ ∈ X` is nontrivial (it does not contain `Z` in its kernel), so by Peterfalvi
(1.1) — "for `|L|` odd a nontrivial irreducible character is non-self-conjugate" — its complex
conjugate `χ̄` differs from `χ`; and `X` is closed under conjugation because `Z` is normal, so
`Ker χ̄ = Ker χ` and `χ̄ ∈ X` whenever `χ ∈ X`.  Thus from one element of the nonempty set `X`
the conjugation involution produces a *second*, distinct one, forcing `|X| ≥ 2` (in fact `|X|`
is even, but only `≥ 2` is used to certify `Z[X, L^#] ≠ 0` and to start the (1.4) prefix).

Stated for an arbitrary finite set of class functions, the two consequences of (1.1) used here —
no real character (`HasNoRealCharacters`) and closure under conjugation (`ClosedUnderConjugate`),
both fields of the §7 `Hypothesis` and inherited by `X ⊆ S` — together with nonemptiness give the
cardinality bound directly. -/
theorem two_le_ncard_of_conjugate_closed_of_noReal
    {X : Set (ClassFunction L ℂ)} (hXfin : X.Finite) (hXne : X.Nonempty)
    (hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate X)
    (hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters X) :
    2 ≤ X.ncard := by
  obtain ⟨χ, hχ⟩ := hXne
  -- `χ̄ ∈ X` by closure under conjugation; `χ̄ ≠ χ` since `χ` is not a real character.
  have hconj_mem : χ.conj ∈ X := hXconj hχ
  have hne : χ.conj ≠ χ := fun h => hXreal hχ h
  -- two distinct members of `X` give `1 < |X|`, i.e. `2 ≤ |X|`.
  have h1 : 1 < X.ncard :=
    (Set.one_lt_ncard hXfin).mpr ⟨χ.conj, hconj_mem, χ, hχ, hne⟩
  omega

/-- The two characters of the `i`-th adjoined pair, as a set `{χᵢ, χ̄ᵢ}`. -/
def pairSet (pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ) (i : ℕ) :
    Set (ClassFunction L ℂ) :=
  {(pair i).1, (pair i).2}

/-- The base set `S₀` together with the pairs `{χⱼ, χ̄ⱼ}` for `j < i`: the set accumulated after
the first `i` adjoinings in the (6.6) "repeated use of (5.6)" induction.

`pairUnion S₀ pair 0 = S₀` and `pairUnion S₀ pair (i+1) = pairUnion S₀ pair i ∪ {χᵢ, χ̄ᵢ}`. -/
def pairUnion (S₀ : Set (ClassFunction L ℂ))
    (pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ) : ℕ → Set (ClassFunction L ℂ)
  | 0 => S₀
  | i + 1 => pairUnion S₀ pair i ∪ pairSet (L := L) pair i

@[simp] theorem pairUnion_zero (S₀ : Set (ClassFunction L ℂ))
    (pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ) :
    pairUnion (L := L) S₀ pair 0 = S₀ := rfl

@[simp] theorem pairUnion_succ (S₀ : Set (ClassFunction L ℂ))
    (pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ) (i : ℕ) :
    pairUnion (L := L) S₀ pair (i + 1) =
      pairUnion (L := L) S₀ pair i ∪ pairSet (L := L) pair i := rfl

theorem subset_pairUnion_succ (S₀ : Set (ClassFunction L ℂ))
    (pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ) (i : ℕ) :
    pairUnion (L := L) S₀ pair i ⊆ pairUnion (L := L) S₀ pair (i + 1) :=
  Set.subset_union_left

theorem pairUnion_mono (S₀ : Set (ClassFunction L ℂ))
    (pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ) {i j : ℕ} (hij : i ≤ j) :
    pairUnion (L := L) S₀ pair i ⊆ pairUnion (L := L) S₀ pair j := by
  induction hij with
  | refl => exact Set.Subset.rfl
  | step _ ih => exact ih.trans (subset_pairUnion_succ (L := L) S₀ pair _)

/-- The `(i+1)`-st accumulator `pairUnion S₀ pair (i+1)` is the `i`-th accumulator with the explicit
two-element set `{c₁, c₂}` adjoined, *provided* the `i`-th pair is `(pair i) = (c₁, c₂)`.

This is the set-level bridge from a per-step adjoining engine — whose conclusion is naturally
phrased
as coherence of `S₁ ∪ {c₁, c₂}` for the adjoined pair — to the `coherentPairChain` accumulator shape
`pairUnion S₀ pair (i+1)`.  With `c₁ = χ`, `c₂ = χ̄` and `(pair i) = (χ, χ̄)`, the two match
definitionally up to the `(pair i).1`/`(pair i).2` rewrites supplied by `hpair0`/`hpair1`. -/
theorem pairUnion_succ_eq_union_pair {S₀ : Set (ClassFunction L ℂ)}
    {pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ} {i : ℕ}
    {c₁ c₂ : ClassFunction L ℂ} (hpair0 : (pair i).1 = c₁) (hpair1 : (pair i).2 = c₂) :
    pairUnion (L := L) S₀ pair (i + 1) = pairUnion (L := L) S₀ pair i ∪ {c₁, c₂} := by
  rw [pairUnion_succ, pairSet, hpair0, hpair1]

/-- Membership in `pairUnion S₀ pair N`: an element is either in the base `S₀` or in one of the
adjoined pairs `{χⱼ, χ̄ⱼ}` with `j < N`. -/
theorem mem_pairUnion {S₀ : Set (ClassFunction L ℂ)}
    {pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ} {χ : ClassFunction L ℂ} {N : ℕ} :
    χ ∈ pairUnion (L := L) S₀ pair N ↔
      χ ∈ S₀ ∨ ∃ j, j < N ∧ χ ∈ pairSet (L := L) pair j := by
  induction N with
  | zero => simp [pairUnion]
  | succ N ih =>
    rw [pairUnion_succ, Set.mem_union, ih]
    constructor
    · rintro ((hS₀ | ⟨j, hjN, hj⟩) | hpair)
      · exact Or.inl hS₀
      · exact Or.inr ⟨j, hjN.trans (Nat.lt_succ_self N), hj⟩
      · exact Or.inr ⟨N, Nat.lt_succ_self N, hpair⟩
    · rintro (hS₀ | ⟨j, hjN, hj⟩)
      · exact Or.inl (Or.inl hS₀)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hjN with hlt | heq
        · exact Or.inl (Or.inr ⟨j, hlt, hj⟩)
        · exact Or.inr (heq ▸ hj)

/-- The pair-chain reaches exactly `X`: if the base `S₀ ⊆ X`, every adjoined pair `pairSet pair j`
(`j < N`) lies in `X`, and conversely every element of `X` is in `S₀` or in some adjoined pair,
then `pairUnion S₀ pair N = X`.

This is the set-theoretic bridge between the `coherentPairChain` engine (which concludes coherence
of the accumulated set `pairUnion S₀ pair N`) and the target set `X = S − S(Z)` of (6.6): the
degree-monotone enumeration of `X` (`exists_monotoneDegreeEnum`) splits `X` into the equal-minimal
-degree prefix `S₀` and the remaining conjugate pairs `{χᵢ, χ̄ᵢ}`, and this lemma certifies that
adjoining those pairs to `S₀` recovers `X`. -/
theorem pairUnion_eq_of_cover {S₀ X : Set (ClassFunction L ℂ)}
    {pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ} {N : ℕ}
    (hS₀ : S₀ ⊆ X) (hpairs : ∀ j, j < N → pairSet (L := L) pair j ⊆ X)
    (hcover : ∀ χ ∈ X, χ ∈ S₀ ∨ ∃ j, j < N ∧ χ ∈ pairSet (L := L) pair j) :
    pairUnion (L := L) S₀ pair N = X := by
  apply Set.Subset.antisymm
  · intro χ hχ
    rcases mem_pairUnion.mp hχ with hbase | ⟨j, hjN, hj⟩
    · exact hS₀ hbase
    · exact hpairs j hjN hj
  · intro χ hχ
    exact mem_pairUnion.mpr (hcover χ hχ)

/-- **Peterfalvi (6.6): the "repeated use of (5.6)" iteration engine.**

Given a coherent base set `S₀` (the equal-minimal-degree prefix coherence supplied by (1.1)+(1.4))
and, for each `i < N`, an adjoining step turning coherence of the set accumulated so far
(`pairUnion S₀ pair i`) into coherence of the set with the `i`-th pair `{χᵢ, χ̄ᵢ}` adjoined
(`pairUnion S₀ pair (i+1)`), the full union after `N` adjoinings, `pairUnion S₀ pair N`, is
coherent.

Each step `hstep i _` is one application of (5.6) (`retarget_isCoherent`); the caller supplies the
per-step (5.6) data (orthonormal `{χᵢ, χ̄ᵢ}`/`{Xᵢ, X̄ᵢ}`, the image equation, the lattice
orthogonalities, the (5.1)-generation) — which references the *current* extension `hcoh.extension`,
hence is given as a function of the running witness, exactly as the induction requires.  This engine
contributes the induction itself: the conclusion `IsCoherent (pairUnion S₀ pair N) A` is **derived**
by recursion on `N`, never assumed. -/
noncomputable def coherentPairChain
    {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (S₀ : Set (ClassFunction L ℂ))
    (pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ)
    (h0 : IsCoherent τ S₀ A) :
    ∀ N : ℕ,
      (∀ i, i < N → IsCoherent τ (pairUnion (L := L) S₀ pair i) A →
        IsCoherent τ (pairUnion (L := L) S₀ pair (i + 1)) A) →
      IsCoherent τ (pairUnion (L := L) S₀ pair N) A
  | 0, _ => h0
  | N + 1, hstep =>
    hstep N (Nat.lt_succ_self N)
      (coherentPairChain S₀ pair h0 N
        (fun i hi => hstep i (hi.trans (Nat.lt_succ_self N))))

/-- **Peterfalvi (6.6): coherence of `X = S − S(Z)`.**

The conclusion of (6.6): the center-conditioned character set `X = {χ ∈ Irr L | Z ⊄ Ker χ}` is
coherent.  This assembles the (6.6) argument's final step "Repeated use of Theorem (5.6) then shows
that `X` is coherent" (mmd L84) by combining the **pair-chain decomposition** of `X` with the
`coherentPairChain` iteration engine.

The hypotheses encode the (6.6) proof structure exactly:
* a degree-ordered **decomposition** of `X` into a base set `S₀` (the equal-minimal-degree prefix
  `{χ₁,…,χₖ}`) and the remaining conjugate pairs `pair j = (χ_{k+j}, χ̄_{k+j})`, certified to
  recover `X` by `pairUnion_eq_of_cover` (`hS₀`, `hpairs`, `hcover`) — the genuinely new content
  here, threading the `exists_monotoneDegreeEnum` sort into the engine's accumulator;
* the **base coherence** `h0 : IsCoherent τ S₀ A`, which (6.6) supplies by (1.1)+(1.4)
  ("By (1.1) and (1.4), `{χ₁,…,χₖ}` is coherent");
* the per-step **(5.6) adjoining** `hstep`, each step one application of (5.6)
  (`retarget_isCoherent`) whose degree inequality `2χᵢ(1)χ₁(1) < ∑_{j<i}χⱼ(1)²` is discharged by
  the gap leaf `two_mul_lt_sq_of_primePow_gap` fed by the degree-sum `sumInflatedDegreeSq`.

`h0` and `hstep` are *supplied* (the base-prefix coherence and the per-step retarget data), not
posited as the result: the conclusion `IsCoherent τ X A` is **derived** from them through the
chain.  See the issue note for the precise residual (the construction of `hstep`'s per-step `{Xᵢ,
X̄ᵢ}` target data needs the Dade-isometry ν basis extension, G2.7). -/
noncomputable def coherentOfPairChainCover
    {τ : IntegralCharacterMap L G} {A : Set L} {X S₀ : Set (ClassFunction L ℂ)}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ) (N : ℕ)
    (hS₀ : S₀ ⊆ X) (hpairs : ∀ j, j < N → pairSet (L := L) pair j ⊆ X)
    (hcover : ∀ χ ∈ X, χ ∈ S₀ ∨ ∃ j, j < N ∧ χ ∈ pairSet (L := L) pair j)
    (h0 : IsCoherent τ S₀ A)
    (hstep : ∀ i, i < N → IsCoherent τ (pairUnion (L := L) S₀ pair i) A →
      IsCoherent τ (pairUnion (L := L) S₀ pair (i + 1)) A) :
    IsCoherent τ X A :=
  pairUnion_eq_of_cover hS₀ hpairs hcover ▸ coherentPairChain S₀ pair h0 N hstep

/-- The pair-chain reaches `X` from a degree-monotone **enumeration** of `X`.

This is the bridge specialized to the way (6.6) actually produces the decomposition: from the
degree-monotone enumeration `e : Fin n → X` of `exists_monotoneDegreeEnum`, which is *surjective*
onto `X` (`hsurj : ∀ χ ∈ X, ∃ i, e i = χ`).  Then the set-level cover hypothesis of
`pairUnion_eq_of_cover` is reduced to the **index-level** cover `hcoverIdx`: each enumerated
character `e i` lies in the base `S₀` or in some adjoined pair.  Surjectivity transports this to
arbitrary `χ ∈ X`, so `pairUnion S₀ pair N = X`.

This is the connective tissue between the `exists_monotoneDegreeEnum` sort and the
`coherentPairChain` accumulator: the enumeration provides facts indexed by `Fin n`, while the
engine's cover is phrased over members of `X`; surjectivity is exactly what closes the gap. -/
theorem pairUnion_eq_of_enumCover {S₀ X : Set (ClassFunction L ℂ)}
    {pair : ℕ → ClassFunction L ℂ × ClassFunction L ℂ} {N : ℕ} {n : ℕ}
    {e : Fin n → ClassFunction L ℂ}
    (hsurj : ∀ χ ∈ X, ∃ i, e i = χ)
    (hS₀ : S₀ ⊆ X) (hpairs : ∀ j, j < N → pairSet (L := L) pair j ⊆ X)
    (hcoverIdx : ∀ i : Fin n,
      e i ∈ S₀ ∨ ∃ j, j < N ∧ e i ∈ pairSet (L := L) pair j) :
    pairUnion (L := L) S₀ pair N = X :=
  pairUnion_eq_of_cover hS₀ hpairs (by
    intro χ hχ
    obtain ⟨i, rfl⟩ := hsurj χ hχ
    exact hcoverIdx i)

end OddOrder.Peterfalvi.S07


