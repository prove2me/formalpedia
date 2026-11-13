-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_GeneralAdjoin
-- name    : OddOrder_Peterfalvi_S08_GeneralAdjoin
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:17:14.45151+00:00
-- url     : https://prove2.me/theorems/fe7c9061-e81b-4265-8b10-efa9925dbe1c
-- title:
--   Peterfalvi (5.6) / Isaacs 7.14: the general mixed-degree coherence adjoin
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §5, (5.6), whose underlying theorem is Isaacs, *Character Theory of Finite Groups*, Theorem 7.14 (mathcomp `extend_coherent`). The Feit–Thompson main text consumes the mixed-degree adjoin in a general form.
--
--   Main definitions: `memberExtensionDecomposition_general` (general member $\psi=0$ decomposition) and `decompositionDaFromDiff_general` (general decomposition for $\chi-a\chi_1$), generalizing the earlier versions.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_GeneralAdjoin.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_GeneralAdjoin.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_BridgeCoherent
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1_CoherentAdjoin

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

/-- **`ℤ[T] ⊆ ℤ[S, A]` when `T ⊆ ℤ[S, A]`.**  The `A`-supported lattice `zSupportedSpan S A`
(`= ℤ[S] ∩ CF(L, A)`) is closed under `ℤ`-combinations, so the span of a subset it contains stays
inside it.  This is what lets the general adjoin's `hisom` (needed on the difference lattices
`ℤ[{χ − χ̄, χ − a·χ₁}]` etc.) be supplied at the Feit–Sibley call site from
`Hypothesis.tau_isometry_diff` (which preserves `⟨·,·⟩` on all of `ℤ[𝒮, A]`): every difference the
engine feeds has its two endpoints in `𝒮`, hence in `ℤ[𝒮, A]`. -/
theorem zSpan_subset_zSupportedSpan {S : Set (ClassFunction L ℂ)} {A : Set L}
    {T : Set (ClassFunction L ℂ)} (hT : ∀ s ∈ T, s ∈ zSupportedSpan (L := L) S A) :
    (Submodule.span ℤ T : Set (ClassFunction L ℂ)) ⊆ zSupportedSpan (L := L) S A := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem s hs => exact hT s hs
  | zero => exact zero_mem_zSupportedSpan
  | add x y _ _ ihx ihy => exact add_mem_zSupportedSpan ihx ihy
  | smul c x _ ih =>
      refine ⟨Submodule.smul_mem _ c ih.1, ?_⟩
      intro t ht
      apply ih.2
      rw [ClassFunction.mem_support] at ht ⊢
      intro hx0
      apply ht
      rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hx0, mul_zero]

/-- **General `inner_Y_extension_member_eq`, rational-degree (scaled-difference) form**
(generalizes `inner_Y_extension_member_eq`, `S08_CoherenceCorePart1/CoherentAdjoin.lean`, to
**arbitrary member degrees** — Isaacs 7.14 / Peterfalvi Lemma 1(a) needs only the anchor
divisibility `χ₀(1) ∣ ψ(1)`, not `χ₀(1) ∣ χ(1)` for every member, so the ratio `χⱼ(1)/χ₁(1)` is
generally
rational).

The integer version used the degree-matched difference `χⱼ − aⱼ·χ₁` (needs `aⱼ = χⱼ(1)/χ₁(1) ∈ ℕ`);
here the **scaled difference `d₁·χⱼ − dⱼ·χ₁`** (`d₁ = χ₁(1)`, `dⱼ = χⱼ(1)`, integer coefficients,
degree `d₁·dⱼ − dⱼ·d₁ = 0`, hence in `ℤ[S₁, A]`) is used instead, so the `ν`-isometry on `ℤ[S₁]`
still applies (`hfound`).  The conclusion is stated in the **division-free scaled form**
`d₁·⟨Y, νχⱼ⟩ = a·d₁·⟨χ₁,χⱼ⟩ − dⱼ·(a·m₁ + μ)` (`μ = ⟨τ(χ−a·χ₁), νχ₁⟩`); the caller
(`crux1_of_memberFamily_general`) divides by `d₁ ≠ 0` to obtain `⟨Y,νχⱼ⟩ = a·[j=1] − λ·(dⱼ/d₁)`. -/
theorem inner_Y_extension_member_eq_general
    {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ : Set (ClassFunction L ℂ)}
    (hS₁ : IsCoherent τ S₁ A)
    (χ : ClassFunction L ℂ) {chi1 cj : ClassFunction L ℂ} {a : ℕ} (d1 dj : ℕ)
    {Xχ Y : ClassFunction G ℂ}
    (hYeq : Y = Xχ - τ (χ - a • chi1))
    (hXortho : ClassFunction.inner Xχ (hS₁.extension cj) = 0)
    (hfound : ClassFunction.inner (τ (χ - a • chi1)) (hS₁.extension (d1 • cj - dj • chi1)) =
      ClassFunction.inner (χ - a • chi1) (d1 • cj - dj • chi1))
    (hχcj : ClassFunction.inner χ cj = 0)
    (hχchi1 : ClassFunction.inner χ chi1 = 0)
    {m₁ : ℂ} (hchi1chi1 : ClassFunction.inner chi1 chi1 = m₁) :
    (d1 : ℂ) * ClassFunction.inner Y (hS₁.extension cj) =
      (a : ℂ) * (d1 : ℂ) * ClassFunction.inner chi1 cj -
        (dj : ℂ) * ((a : ℂ) * m₁ + ClassFunction.inner (τ (χ - a • chi1))
          (hS₁.extension chi1)) := by
  -- `⟨Y, νχⱼ⟩ = −⟨τ(χ−a·χ₁), νχⱼ⟩` (`Xχ ⊥ νχⱼ`).
  have hY0 : ClassFunction.inner Y (hS₁.extension cj) =
      -ClassFunction.inner (τ (χ - a • chi1)) (hS₁.extension cj) := by
    rw [hYeq, ClassFunction.inner_sub_left, hXortho, zero_sub]
  -- LHS of `hfound`: `⟨τ(χ−a·χ₁), ν(d₁·χⱼ − dⱼ·χ₁)⟩ = d₁·⟨·,νχⱼ⟩ − dⱼ·⟨·,νχ₁⟩`.
  have hνexp : hS₁.extension (d1 • cj - dj • chi1) =
      (d1 : ℂ) • hS₁.extension cj - (dj : ℂ) • hS₁.extension chi1 := by
    rw [map_sub, map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ d1 (hS₁.extension cj),
      ← Nat.cast_smul_eq_nsmul ℂ dj (hS₁.extension chi1)]
  have hlhs : ClassFunction.inner (τ (χ - a • chi1)) (hS₁.extension (d1 • cj - dj • chi1)) =
      (d1 : ℂ) * ClassFunction.inner (τ (χ - a • chi1)) (hS₁.extension cj) -
        (dj : ℂ) * ClassFunction.inner (τ (χ - a • chi1)) (hS₁.extension chi1) := by
    rw [hνexp, ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast, star_natCast]
  -- RHS of `hfound`: the source expansion.
  have hrhs : ClassFunction.inner (χ - a • chi1) (d1 • cj - dj • chi1) =
      -((a : ℂ) * (d1 : ℂ)) * ClassFunction.inner chi1 cj + (a : ℂ) * (dj : ℂ) * m₁ := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a chi1, ← Nat.cast_smul_eq_nsmul ℂ d1 cj,
      ← Nat.cast_smul_eq_nsmul ℂ dj chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχcj, hχchi1, hchi1chi1, star_natCast]
    ring
  rw [hlhs, hrhs] at hfound
  -- `d₁·⟨τ(χ−a·χ₁),νχⱼ⟩ = dⱼ·μ − a·d₁·⟨χ₁,χⱼ⟩ + a·dⱼ·m₁`; multiply `hY0` by `d₁`.
  rw [hY0]
  ring_nf
  ring_nf at hfound
  linear_combination -hfound

/-- **General member `ψ = 0` decomposition** (generalizes `memberExtensionDecomposition`,
`S08_YsetInner`).  For a member `χ ∈ S₁` (with `χ̄ ∈ S₁`) and its `R(χ)` family, the (5.5)
decomposition of `χ` uses the **running extension `ν = hS₁.extension` as the auxiliary isometry**
(not `τ`): `ν χ ∈ ℤ[Irr G]` (`hνZ`, since `χ ∈ S₁`) whereas `τ χ` need not be integral, and `ν`
agrees with `τ` on the supported difference `χ − χ̄`.  The `R(χ)` family is w.r.t. `τ`
(supplied from `Hypothesis.difference_image`). -/
noncomputable def memberExtensionDecomposition_general
    {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ : Set (ClassFunction L ℂ)}
    (hS₁ : IsCoherent τ S₁ A) {χ : ClassFunction L ℂ}
    (imageFamily : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (hdiffsupp : (χ.conj - χ).support ⊆ A)
    (hχ_S1 : χ ∈ S₁) (hχbar_S1 : χ.conj ∈ S₁)
    (hνZ : hS₁.extension χ ∈ ZIrr G)
    (hχχbar : ClassFunction.inner χ χ.conj = 0) :
    CharacterPsiDecomposition (L := L) (G := G) τ χ 0 := by
  classical
  have hχmem : χ ∈ Submodule.span ℤ S₁ := Submodule.subset_span hχ_S1
  have hχbarmem : χ.conj ∈ Submodule.span ℤ S₁ := Submodule.subset_span hχbar_S1
  have hle : Submodule.span ℤ ({χ - χ.conj, χ - 0} : Set (ClassFunction L ℂ)) ≤
      Submodule.span ℤ S₁ := by
    rw [Submodule.span_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Submodule.sub_mem _ hχmem hχbarmem
    · rw [sub_zero]; exact hχmem
  have hdiffsupported : χ - χ.conj ∈ zSupportedSpan (L := L) S₁ A :=
    mem_zSupportedSpan_iff.mpr ⟨Submodule.sub_mem _ hχmem hχbarmem, by
      rw [show χ - χ.conj = -(χ.conj - χ) from by abel, ClassFunction.support_neg]
      exact hdiffsupp⟩
  exact CharacterPsiDecomposition.ofProjection imageFamily hS₁.extension
    (fun φ ζ hφ hζ => hS₁.extension_inner_eq φ ζ (hle hφ) (hle hζ))
    (hS₁.extends_on_supported _ hdiffsupported)
    (by rw [sub_zero]; exact hνZ)
    (by simp) (by simp) hχχbar

/-- **General χ decomposition for `χ − a·χ₁`** (generalizes `decompositionDaFromDadeOfDiff`,
`S07_Coherence/FamilyBundleDade`).  Uses `ofProjection` with the auxiliary isometry `τ` itself,
whose inner-preservation is needed only on the supported **difference** lattice `{χ − χ̄, χ − a·χ₁}`
(`hisom`), and the `ZIrr`-membership only on `χ − a·χ₁` (`hτaχ1Z`).  Works for an unsupported `χ`
(e.g. `χ = Ind θ`). -/
noncomputable def decompositionDaFromDiff_general
    {τ : IntegralCharacterMap L G} {A : Set L} {Samb : Set (ClassFunction L ℂ)}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {χ chi1 : ClassFunction L ℂ} {a : ℕ}
    (imageFamily : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (hisom : ∀ (T : Set (ClassFunction L ℂ)), (∀ s ∈ T, s ∈ zSupportedSpan (L := L) Samb A) →
      ∀ φ ζ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (hdiffmem : χ - χ.conj ∈ zSupportedSpan (L := L) Samb A)
    (hadiffmem : χ - a • chi1 ∈ zSupportedSpan (L := L) Samb A)
    (hτaχ1Z : τ (χ - a • chi1) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner χ (a • chi1 : ClassFunction L ℂ) = 0)
    (hχbaraχ1 : ClassFunction.inner χ.conj (a • chi1 : ClassFunction L ℂ) = 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0) :
    CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1) := by
  classical
  have hSdiff : ∀ s ∈ ({χ - χ.conj, χ - a • chi1} : Set (ClassFunction L ℂ)),
      s ∈ zSupportedSpan (L := L) Samb A := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hdiffmem
    · exact hadiffmem
  exact CharacterPsiDecomposition.ofProjection imageFamily τ
    (fun φ ζ hφ hζ => hisom _ hSdiff φ ζ hφ hζ)
    rfl hτaχ1Z hχaχ1 hχbaraχ1 hχχbar

end OddOrder.Peterfalvi.S07


