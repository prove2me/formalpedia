-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S03b_Vanishing
-- name    : OddOrder_Peterfalvi_S03b_Vanishing
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:42:42.563654+00:00
-- url     : https://prove2.me/theorems/0e1e5bb0-eb6a-498f-950f-3017be770ad1
-- title:
--   Peterfalvi (1.2): vanishing of an irreducible character off trivial subgroup-centralizers
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §3, p. 5, statement (1.2), the keystone vanishing lemma: if $H\trianglelefteq G$, $\chi\in\mathrm{Irr}(G)$ does not have $H$ in its kernel, and $g\in G$ has trivial centralizer in $H$ ($C_H(g)=1$), then $\chi(g)=0$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S03b_Vanishing.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S03b_Vanishing.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S03_PreliminaryCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality

namespace OddOrder.Peterfalvi.S03

open OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G] [Finite G]

/-- If `C_H(g) = 1` for a normal subgroup `H ⊴ G`, the quotient map `G → G ⧸ H`
restricts to an injection on `C_G(g)` whose image centralizes `ḡ`, so
`|C_G(g)| ≤ |C_{G ⧸ H}(ḡ)|`.

This is the centralizer inequality `|C_G(g)| = |C_G(g)H/H| ≤ |C_{G ⧸ H}(ḡ)|` used in
the proof of Peterfalvi (1.2). -/
theorem card_centralizer_le_card_centralizer_quotient
    {H : Subgroup G} [H.Normal] {g : G}
    (hCH : centralizerInSubgroup H g = ⊥) :
    Nat.card (Subgroup.centralizer ({g} : Set G)) ≤
      Nat.card (Subgroup.centralizer
        ({(QuotientGroup.mk g : G ⧸ H)} : Set (G ⧸ H))) := by
  classical
  set C := Subgroup.centralizer ({g} : Set G) with hCdef
  -- the restriction of the quotient map to `C`
  let φ : C →* G ⧸ H := (QuotientGroup.mk' H).comp C.subtype
  -- `φ` is injective: an element of its kernel lies in `C ⊓ H = C_H(g) = ⊥`
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hx⟩ hxk
    have hxH : x ∈ H := by
      have hx1 : (QuotientGroup.mk' H) x = 1 := hxk
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    have hxg : x * g = g * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hxmem : x ∈ centralizerInSubgroup H g := by
      rw [mem_centralizerInSubgroup]; exact ⟨hxH, hxg⟩
    rw [hCH, Subgroup.mem_bot] at hxmem
    simp only [Subgroup.mem_bot]
    exact Subtype.ext hxmem
  -- the image of `φ` centralizes `ḡ`
  have hrange : φ.range ≤
      Subgroup.centralizer ({(QuotientGroup.mk g : G ⧸ H)} : Set (G ⧸ H)) := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxg : x * g = g * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    change (QuotientGroup.mk' H) x * QuotientGroup.mk g
        = QuotientGroup.mk g * (QuotientGroup.mk' H) x
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxg]
  calc Nat.card C = Nat.card φ.range :=
        Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
    _ ≤ Nat.card (Subgroup.centralizer
          ({(QuotientGroup.mk g : G ⧸ H)} : Set (G ⧸ H))) :=
        Nat.card_mono (Set.toFinite _) (SetLike.coe_subset_coe.mpr hrange)

/-- **Peterfalvi (1.2)**.  Let `H ⊴ G`, let `χ ∈ Irr(G)` be such that `H ⊄ ker χ`
(expressed at the class-function level by `¬ (H ⊆ characterKernel χ)`), and let
`g ∈ G` be such that `C_H(g) = 1`.  Then `χ(g) = 0`. -/
theorem irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot
    {H : Subgroup G} [H.Normal] (χ : IrreducibleCharacter G)
    (hker : ¬ ((H : Set G) ⊆ characterKernel (χ : ClassFunction G ℂ)))
    {g : G} (hCH : centralizerInSubgroup H g = ⊥) :
    (χ : ClassFunction G ℂ) g = 0 := by
  classical
  have : Finite (G ⧸ H) :=
    Finite.of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  -- real-valued summand `f ψ = |ψ(g)|²`
  set f : IrreducibleCharacter G → ℝ :=
    fun ψ => Complex.normSq ((ψ : ClassFunction G ℂ) g) with hf
  have hf_nonneg : ∀ ψ, 0 ≤ f ψ := fun ψ => Complex.normSq_nonneg _
  -- (A) total sum over `Irr G` equals `|C_G(g)|`
  have hA : ∑ ψ : IrreducibleCharacter G, f ψ
      = (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ) := by
    have key := column_orthogonality_diagonal (G := G) g
    have e : ∀ ψ : IrreducibleCharacter G,
        (ψ : ClassFunction G ℂ) g * star ((ψ : ClassFunction G ℂ) g) = (↑(f ψ) : ℂ) := by
      intro ψ
      have h := Complex.mul_conj ((ψ : ClassFunction G ℂ) g)
      rwa [starRingEnd_apply] at h
    rw [Finset.sum_congr rfl (fun ψ _ => e ψ), ← Complex.ofReal_sum] at key
    exact_mod_cast key
  -- the kernel-containing subset of `Irr G`
  set s : Finset (IrreducibleCharacter G) :=
    Finset.univ.filter (fun ψ => (H : Set G) ⊆ characterKernel (ψ : ClassFunction G ℂ))
    with hs
  -- (B) the sum over `s` equals `|C_{G ⧸ H}(ḡ)|` via inflation
  have hB : ∑ ψ ∈ s, f ψ
      = (Nat.card (Subgroup.centralizer
          ({(QuotientGroup.mk g : G ⧸ H)} : Set (G ⧸ H))) : ℝ) := by
    -- `s` is exactly the image of inflation
    have himg : s = Finset.univ.image (inflate H) := by
      ext ψ
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hψ
        obtain ⟨φ, hφ⟩ := exists_inflate_eq_of_subset_characterKernel (N := H) ψ hψ
        exact ⟨φ, hφ⟩
      · rintro ⟨φ, rfl⟩
        exact subset_characterKernel_inflate (N := H) φ
    rw [himg, Finset.sum_image (fun a _ b _ h => inflate_injective H h)]
    -- value preservation: `f (inflate H φ) = |φ(ḡ)|²`
    have e2 : ∀ φ : IrreducibleCharacter (G ⧸ H),
        f (inflate H φ)
          = Complex.normSq ((φ : ClassFunction (G ⧸ H) ℂ) (QuotientGroup.mk g)) := by
      intro φ
      simp only [hf, inflate_apply, QuotientGroup.mk'_apply]
    rw [Finset.sum_congr rfl (fun φ _ => e2 φ)]
    -- column orthogonality on `G ⧸ H`
    have key := column_orthogonality_diagonal (G := G ⧸ H) (QuotientGroup.mk g)
    have e : ∀ φ : IrreducibleCharacter (G ⧸ H),
        (φ : ClassFunction (G ⧸ H) ℂ) (QuotientGroup.mk g)
            * star ((φ : ClassFunction (G ⧸ H) ℂ) (QuotientGroup.mk g))
          = (↑(Complex.normSq
              ((φ : ClassFunction (G ⧸ H) ℂ) (QuotientGroup.mk g))) : ℂ) := by
      intro φ
      have h := Complex.mul_conj ((φ : ClassFunction (G ⧸ H) ℂ) (QuotientGroup.mk g))
      rwa [starRingEnd_apply] at h
    rw [Finset.sum_congr rfl (fun φ _ => e φ), ← Complex.ofReal_sum] at key
    exact_mod_cast key
  -- (C) centralizer inequality
  have hC : (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ)
      ≤ (Nat.card (Subgroup.centralizer
          ({(QuotientGroup.mk g : G ⧸ H)} : Set (G ⧸ H))) : ℝ) := by
    exact_mod_cast card_centralizer_le_card_centralizer_quotient (H := H) hCH
  -- squeeze: `∑_{Irr G} f = ∑_s f`
  have hsubset : s ⊆ Finset.univ := Finset.subset_univ s
  have hle : ∑ ψ ∈ s, f ψ ≤ ∑ ψ : IrreducibleCharacter G, f ψ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun ψ _ _ => hf_nonneg ψ)
  have hge : ∑ ψ : IrreducibleCharacter G, f ψ ≤ ∑ ψ ∈ s, f ψ := by
    rw [hA, hB]; exact hC
  have hsqueeze : ∑ ψ : IrreducibleCharacter G, f ψ = ∑ ψ ∈ s, f ψ :=
    le_antisymm hge hle
  -- the complement terms sum to zero
  have hsd := Finset.sum_sdiff (f := f) hsubset
  have hsdiff : ∑ ψ ∈ Finset.univ \ s, f ψ = 0 := by linarith [hsd, hsqueeze]
  -- `χ` lies in the complement, so its term vanishes
  have hχs : χ ∉ s := by
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hker
  have hχmem : χ ∈ Finset.univ \ s := Finset.mem_sdiff.mpr ⟨Finset.mem_univ χ, hχs⟩
  have hfχ : f χ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun ψ _ => hf_nonneg ψ)).mp hsdiff χ hχmem
  exact Complex.normSq_eq_zero.mp hfχ

end OddOrder.Peterfalvi.S03


