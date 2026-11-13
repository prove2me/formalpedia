-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_BridgeCoherent
-- name    : OddOrder_Peterfalvi_S07_BridgeCoherent
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:06:43.715763+00:00
-- url     : https://prove2.me/theorems/3701eeac-9eca-4fd9-9d90-abfc26597eb8
-- title:
--   Peterfalvi §5/§7: the bridge gluing lemma for coherence (`bridge_coherent`)
-- statement:
--   Ports mathcomp's `bridge_coherent` (Peterfalvi §5), used by the (11.8) capstone, to the Lean `IsCoherent` interface: coherence of a union $X\cup Y$ of two coherent sets obtained by gluing along a single bridge.
--
--   The main definition is `coherentUnion_of_glued_of_bridge`, coherence of $X\cup Y$ from a single bridge.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_BridgeCoherent.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_BridgeCoherent.lean
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

open OddOrder.Peterfalvi.S03

variable {L G : Type*} [Group L] [Group G]

theorem characterDegree_add (φ ψ : ClassFunction L ℂ) :
    characterDegree (φ + ψ) = characterDegree φ + characterDegree ψ := by
  simp [characterDegree_def]

theorem characterDegree_sub (φ ψ : ClassFunction L ℂ) :
    characterDegree (φ - ψ) = characterDegree φ - characterDegree ψ := by
  simp [characterDegree_def]

theorem characterDegree_zsmul (n : ℤ) (φ : ClassFunction L ℂ) :
    characterDegree (n • φ) = (n : ℂ) * characterDegree φ := by
  rw [← Int.cast_smul_eq_zsmul ℂ n φ]
  simp [characterDegree_def]

/-- Within a lattice `ℤ[X]` of integer-degree class functions, every element has integer degree. -/
theorem exists_intDegree_of_mem_span {X : Set (ClassFunction L ℂ)}
    (hdeg : ∀ x ∈ X, ∃ n : ℤ, characterDegree x = (n : ℂ))
    {ζ : ClassFunction L ℂ} (hζ : ζ ∈ Submodule.span ℤ X) :
    ∃ n : ℤ, characterDegree ζ = (n : ℂ) := by
  induction hζ using Submodule.span_induction with
  | mem x hx => exact hdeg x hx
  | zero => exact ⟨0, by simp [characterDegree_def]⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx; obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by rw [characterDegree_add, ha, hb]; push_cast; ring⟩
  | smul c x _ ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨c * a, by rw [characterDegree_zsmul, ha]; push_cast; ring⟩

/-- `A`-supported (with `1 ∉ A`) forces degree `0`: this is the `A = L^#` half of the degree/support
dictionary. -/
theorem characterDegree_eq_zero_of_mem_zSupportedSpan {S : Set (ClassFunction L ℂ)} {A : Set L}
    (h1A : (1 : L) ∉ A) {φ : ClassFunction L ℂ} (hφ : φ ∈ zSupportedSpan (L := L) S A) :
    characterDegree φ = 0 := by
  rw [characterDegree_def]
  by_contra h
  exact h1A (hφ.2 (ClassFunction.mem_support.mpr h))

/-- **mathcomp `bridge_coherent` (Coq `PFsection5.v:1000`) — coherence of `X ∪ Y` from a single
`A`-supported bridge, no generation hypothesis.**

Given two coherent families `X`, `Y` with a glued extension `ν` (agreeing with `hX.extension` on
`X`, `hY.extension` on `Y`), mutually orthogonal in source (`hsrc_ortho`) and image (`hmixed`, which
with `hsrc_ortho` gives image orthogonality), and a **single** bridge `χ − φ` (`χ ∈ X`, `φ ∈ ℤ[Y]`,
`A`-supported, `ν(χ − φ) = τ(χ − φ)`), the union `X ∪ Y` is coherent with extension `ν`.

Unlike `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`, this needs **no**
generation hypothesis: the `extends_on_supported` obligation is discharged by Coq's descaling
identity
(`PFsection5.v:1044–1051`), which multiplies by `χ(1)` and cancels through the bridge.

The degree/support structure that Coq draws from the ambient `subcoherent S` (`A = L^#`, characters)
appears explicitly: `h1A` (`1 ∉ A`), `hsuppX`/`hsuppY` (degree `0` ⇒ `A`-supported inside each
lattice), `hdegX`/`hdegY`/`hdegχ` (integer degrees). -/
noncomputable def coherentUnion_of_glued_of_bridge
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
    -- degree/support dictionary (Coq: ambient `subcoherent S` with `A = L^#`)
    (h1A : (1 : L) ∉ A)
    (hdegX : ∀ x ∈ X, ∃ n : ℤ, characterDegree x = (n : ℂ))
    (hdegY : ∀ y ∈ Y, ∃ n : ℤ, characterDegree y = (n : ℂ))
    (hsuppX : ∀ ζ ∈ Submodule.span ℤ X, characterDegree ζ = 0 →
      ζ ∈ zSupportedSpan (L := L) X A)
    (hsuppY : ∀ ζ ∈ Submodule.span ℤ Y, characterDegree ζ = 0 →
      ζ ∈ zSupportedSpan (L := L) Y A)
    -- the single bridge (replaces the false generation hypothesis)
    (χ φ : ClassFunction L ℂ) (hχX : χ ∈ X) (hφY : φ ∈ Submodule.span ℤ Y)
    (hdegχ : characterDegree χ ≠ 0)
    (hbridge_supp : χ - φ ∈ zSupportedSpan (L := L) (X ∪ Y) A)
    (hbridge_τ : ν (χ - φ) = τ (χ - φ)) :
    IsCoherent τ (X ∪ Y) A := by
  classical
  -- span-lifted agreements of `ν` with the two extensions.
  have hagreeX' : ∀ u ∈ Submodule.span ℤ X, ν u = hX.extension u :=
    fun u hu => IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeX hu
  have hagreeY' : ∀ v ∈ Submodule.span ℤ Y, ν v = hY.extension v :=
    fun v hv => IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeY hv
  refine ⟨?_, ν, ?_, ?_, ?_⟩
  · -- nonzero: inherited from `X ⊆ X ∪ Y`.
    obtain ⟨ψ, hψmem, hψne⟩ := hX.nonzero
    exact ⟨ψ, zSupportedSpan_mono_left Set.subset_union_left hψmem, hψne⟩
  · -- `extension_inner_eq`: the two-lattice gluing identity (generation-independent).
    intro ψ₁ ψ₂ hψ₁ hψ₂
    exact inner_eq_on_zSpan_union_of_orthogonal hagreeX' hagreeY'
      hX.extension_inner_eq hY.extension_inner_eq hsrc_ortho
      (image_orthogonal_of_mixed_inner_eq hagreeX' hagreeY'
        (mixed_inner_eq_on_zSpan_of_eq_on hmixed) hsrc_ortho)
      hψ₁ hψ₂
  · -- `extends_on_supported`: **Coq's descaling identity** — no generation hypothesis.
    intro η hη
    -- decompose `η = η₁ + η₂` with `η₁ ∈ ℤ[X]`, `η₂ ∈ ℤ[Y]`.
    have hmem : η ∈ Submodule.span ℤ X ⊔ Submodule.span ℤ Y := by
      rw [← Submodule.span_union]; exact hη.1
    obtain ⟨η1, hη1, η2, hη2, rfl⟩ := Submodule.mem_sup.mp hmem
    -- integer degrees of the anchor and of the two pieces.
    obtain ⟨n, hn_eq⟩ := hdegX χ hχX
    obtain ⟨m1, hm1⟩ := exists_intDegree_of_mem_span hdegX hη1
    obtain ⟨m2, hm2⟩ := exists_intDegree_of_mem_span hdegY hη2
    have hn0C : (n : ℂ) ≠ 0 := hn_eq ▸ hdegχ
    -- degree `0` of the supported `η`, and the bridge degree match `φ(1) = χ(1)`.
    have hdegη : characterDegree (η1 + η2) = 0 :=
      characterDegree_eq_zero_of_mem_zSupportedSpan h1A hη
    have hsum0 : (m1 : ℂ) + (m2 : ℂ) = 0 := by
      rw [← hm1, ← hm2, ← characterDegree_add]; exact hdegη
    have hm2_eq : m2 = -m1 := by
      have hz : (m1 + m2 : ℤ) = 0 := by exact_mod_cast hsum0
      omega
    have hdegbridge : characterDegree (χ - φ) = 0 :=
      characterDegree_eq_zero_of_mem_zSupportedSpan h1A hbridge_supp
    have hdegφ : characterDegree φ = (n : ℂ) := by
      rw [characterDegree_sub, sub_eq_zero] at hdegbridge
      rw [← hdegbridge]; exact hn_eq
    -- the two "off-support" brackets `n•η_i − m_i•(anchor)`, each `A`-supported (degree `0`).
    have hB1span : n • η1 - m1 • χ ∈ Submodule.span ℤ X :=
      Submodule.sub_mem _ (Submodule.smul_mem _ n hη1)
        (Submodule.smul_mem _ m1 (Submodule.subset_span hχX))
    have hB1deg : characterDegree (n • η1 - m1 • χ) = 0 := by
      rw [characterDegree_sub, characterDegree_zsmul, characterDegree_zsmul, hm1, hn_eq]; ring
    have hB1supp : n • η1 - m1 • χ ∈ zSupportedSpan (L := L) X A := hsuppX _ hB1span hB1deg
    have hB2span : n • η2 - m2 • φ ∈ Submodule.span ℤ Y :=
      Submodule.sub_mem _ (Submodule.smul_mem _ n hη2) (Submodule.smul_mem _ m2 hφY)
    have hB2deg : characterDegree (n • η2 - m2 • φ) = 0 := by
      rw [characterDegree_sub, characterDegree_zsmul, characterDegree_zsmul, hm2, hdegφ]; ring
    have hB2supp : n • η2 - m2 • φ ∈ zSupportedSpan (L := L) Y A := hsuppY _ hB2span hB2deg
    -- on each bracket, the extension agrees with `τ` (coherence of `X`, `Y`); expand to atoms.
    have E1 : n • hX.extension η1 = n • τ η1 - m1 • τ χ + m1 • hX.extension χ := by
      have h := hX.extends_on_supported _ hB1supp
      simp only [map_sub, map_zsmul] at h
      rw [← h]; abel
    have E2 : n • hY.extension η2 = n • τ η2 - m2 • τ φ + m2 • hY.extension φ := by
      have h := hY.extends_on_supported _ hB2supp
      simp only [map_sub, map_zsmul] at h
      rw [← h]; abel
    have RHSeq : n • τ (η1 + η2) = n • τ η1 + n • τ η2 := by rw [map_add, smul_add]
    -- the bridge, in image form: `τ χ − τ φ = (hX.extension χ) − (hY.extension φ)`.
    have hbr : τ (χ - φ) = hX.extension χ - hY.extension φ := by
      rw [← hbridge_τ, map_sub, hagreeX χ hχX, hagreeY' φ hφY]
    have hextχ : hX.extension χ = τ χ - τ φ + hY.extension φ := by
      have hbr' : τ χ - τ φ = hX.extension χ - hY.extension φ := by rw [← map_sub]; exact hbr
      rw [hbr']; abel
    have hνη : ν (η1 + η2) = hX.extension η1 + hY.extension η2 := by
      rw [map_add, hagreeX' η1 hη1, hagreeY' η2 hη2]
    -- the descaled identity: `n • (ν η) = n • (τ η)`; the bridge kills the anchor terms.
    have key : n • (hX.extension η1 + hY.extension η2) = n • τ (η1 + η2) := by
      rw [smul_add, E1, E2, RHSeq, hextχ, hm2_eq]
      simp only [smul_add, smul_sub, neg_smul]
      abel
    -- cancel the nonzero integer `n = χ(1)`.
    rw [hνη]
    rw [← Int.cast_smul_eq_zsmul ℂ n (hX.extension η1 + hY.extension η2),
      ← Int.cast_smul_eq_zsmul ℂ n (τ (η1 + η2))] at key
    exact smul_right_injective (ClassFunction G ℂ) hn0C key
  · -- `extension_mem_ZIrr`: each generator maps via the two extensions into `ℤ[Irr G]`.
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hyX | hyY
        · rw [hagreeX' y (Submodule.subset_span hyX)]
          exact hX.extension_mem_ZIrr y (Submodule.subset_span hyX)
        · rw [hagreeY' y (Submodule.subset_span hyY)]
          exact hY.extension_mem_ZIrr y (Submodule.subset_span hyY)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
    | smul c y _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ c ih

end OddOrder.Peterfalvi.S07


