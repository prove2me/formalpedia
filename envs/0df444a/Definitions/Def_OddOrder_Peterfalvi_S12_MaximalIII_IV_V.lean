-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V
-- name    : OddOrder_Peterfalvi_S12_MaximalIII_IV_V
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:27:31.912167+00:00
-- url     : https://prove2.me/theorems/8ff48c4c-c31d-4f4c-bcdd-1d525927ee95
-- title:
--   Peterfalvi (11.8.5): parity and real-column facts for maximal types III, IV, V (continuation)
-- statement:
--   A continuation file for Peterfalvi (11.8.5): parity of inner products of real virtual characters and the reality of the $\sigma$-column sum $\sum_r \omega_{r0}^\sigma$, assembling the step that the integer $a$ is even.
--
--   Main declarations: `even_inner_of_conjPerm_symmetric` (Parity of the inner product of two real virtual characters orthogonal to `1`); `Hypothesis.sum_alignedOmegaSigma_zeroColumn_isReal` (The `σ`-column sum `∑_r ω_{r0}^σ` is real); `Hypothesis.a_even_of_eq_inner_sumOmegaSigma` (Peterfalvi (11.8.5), the "`a` even" step); `Hypothesis.beta_inner_trivial` (Peterfalvi (11.8.5), `β ⊥ 1_G`).
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_Props109To1011
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalTypesSetup
import Definitions.Def_OddOrder_Peterfalvi_S10_Theorem88CaseB

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Parity of a sum over a fixed-point-free involution** with an involution-invariant integer
weight.  If `g` is a fixed-point-free involution on `s` and `f (g a) = f a` for all `a ∈ s`, then
`∑_{a ∈ s} f a` is even — each orbit `{a, g a}` contributes `2·f a`.  (Proof via `ZMod 2`:
`(f a : ZMod 2) + (f (g a) : ZMod 2) = 2·(f a) = 0`, so `Finset.sum_involution` kills the sum mod
2.)
This is the combinatorial core of the Peterfalvi (11.8.5) "`a` even from `β` real" parity — the
conjugation involution `χ ↦ χ̄` on `Irr G ∖ {1}` is fixed-point-free by Peterfalvi (1.1). -/
theorem even_sum_of_involution {α : Type*} {s : Finset α} {f : α → ℤ}
    (g : ∀ a ∈ s, α) (g_mem : ∀ a ha, g a ha ∈ s) (g_ne : ∀ a ha, g a ha ≠ a)
    (g_inv : ∀ a ha, g (g a ha) (g_mem a ha) = a) (hf : ∀ a ha, f (g a ha) = f a) :
    Even (∑ a ∈ s, f a) := by
  suffices h : ((∑ a ∈ s, f a : ℤ) : ZMod 2) = 0 by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by push_cast at hk; omega⟩
  rw [Int.cast_sum]
  refine Finset.sum_involution g ?_ (fun a ha _ => g_ne a ha) g_mem g_inv
  intro a ha
  rw [hf a ha]
  exact CharTwo.add_self_eq_zero _

/-- **Inner product of two conjugated class functions** `⟨φ̄, ψ̄⟩ = conj ⟨φ, ψ⟩`.  Pointwise:
`∑_g star(φ g)·ψ g = conj (∑_g φ g · star(ψ g))`, and `⅟|G|` is real. -/
theorem inner_conj_conj [Fintype G] [Invertible (Nat.card G : ℂ)] (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner φ.conj ψ.conj = star (ClassFunction.inner φ ψ) := by
  have hsum : ClassFunction.innerSum φ.conj ψ.conj = star (ClassFunction.innerSum φ ψ) := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, star_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ClassFunction.conj_apply, ClassFunction.conj_apply, star_mul, star_star, mul_comm]
  have hcard : (Nat.card G : ℂ) ≠ 0 := (isUnit_of_invertible (Nat.card G : ℂ)).ne_zero
  refine mul_left_cancel₀ hcard ?_
  rw [ClassFunction.card_mul_inner, hsum, ← ClassFunction.card_mul_inner, star_mul, star_natCast,
    mul_comm]

/-- For a **real** `Δ ∈ ZIrr G`, the Fourier coefficient is `conjPerm`-symmetric:
`⟨Δ, χ̄⟩ = ⟨Δ, χ⟩`.  Since `Δ̄ = Δ` (`IsReal`), `⟨Δ, χ̄⟩ = ⟨Δ̄, χ̄⟩ = conj⟨Δ,χ⟩`
(`inner_conj_conj`),
and `⟨Δ,χ⟩` is a real integer (`mem_ZIrr_inner_int`), so the `conj` is inert. -/
theorem inner_conjPerm_eq_of_isReal [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {Δ : ClassFunction G ℂ} (hΔ : Δ ∈ ZIrr G) (hr : ClassFunction.IsReal Δ)
    (χ : IrreducibleCharacter G) :
    ClassFunction.inner Δ
        ((IrreducibleCharacter.conjPerm G χ : IrreducibleCharacter G) : ClassFunction G ℂ)
      = ClassFunction.inner Δ (χ : ClassFunction G ℂ) := by
  rw [IrreducibleCharacter.conjPerm_apply_coe]
  have key : ClassFunction.inner Δ ((χ : ClassFunction G ℂ).conj)
      = ClassFunction.inner Δ.conj ((χ : ClassFunction G ℂ).conj) := by rw [hr]
  rw [key, inner_conj_conj]
  obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ hΔ
  rw [hm, star_intCast]

open scoped Classical in
/-- **Parity of the inner product of two real virtual characters orthogonal to `1`** (Peterfalvi
(11.8.5) "`a` even from `β` real").  For `Δ₁, Δ₂ ∈ ZIrr G` (odd `G`) that are real (`IsReal`) —
hence
with `conjPerm`-symmetric Fourier coefficients `⟨Δᵢ, χ̄⟩ = ⟨Δᵢ, χ⟩` — with `⟨Δ₂, 1⟩ = 0` (only one
factor need be orthogonal to `1`, since the `χ = 1` term `c₁(1)·c₂(1)` vanishes), the integer
`⟨Δ₁, Δ₂⟩` is even.  Cross-Parseval (`mem_ZIrr_inner_eq_sum_over_irr`) gives
`⟨Δ₁,Δ₂⟩ = ∑_χ c₁(χ)c₂(χ)` with `cᵢ(χ) = ⟨Δᵢ,χ⟩ ∈ ℤ`; the `χ = 1` term vanishes, and on `Irr ∖ {1}`
the conjugation involution `conjPerm` is fixed-point-free (`conjPerm_eq_self_iff` +
`not_isReal_of_ne_trivial_of_odd_card'`) with `cᵢ` invariant, so `even_sum_of_involution`
applies. -/
theorem even_inner_of_conjPerm_symmetric [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (hodd : Odd (Nat.card G))
    {Δ₁ Δ₂ : ClassFunction G ℂ} (h₁ : Δ₁ ∈ ZIrr G) (h₂ : Δ₂ ∈ ZIrr G)
    (hr₁ : ClassFunction.IsReal Δ₁) (hr₂ : ClassFunction.IsReal Δ₂)
    (htriv₂ : ClassFunction.inner Δ₂ (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0) :
    ∃ z : ℤ, ClassFunction.inner Δ₁ Δ₂ = (z : ℂ) ∧ Even z := by
  have hsym₁ := fun χ => inner_conjPerm_eq_of_isReal h₁ hr₁ χ
  have hsym₂ := fun χ => inner_conjPerm_eq_of_isReal h₂ hr₂ χ
  choose c₁ hc₁ using fun χ : IrreducibleCharacter G =>
    OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ h₁
  choose c₂ hc₂ using fun χ : IrreducibleCharacter G =>
    OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ h₂
  have hz : ClassFunction.inner Δ₁ Δ₂
      = ((∑ χ : IrreducibleCharacter G, c₁ χ * c₂ χ : ℤ) : ℂ) := by
    rw [mem_ZIrr_inner_eq_sum_over_irr h₂]
    push_cast
    exact Finset.sum_congr rfl fun χ _ => by rw [hc₁ χ, hc₂ χ]
  refine ⟨_, hz, ?_⟩
  have hc2t : c₂ (trivialIrreducibleCharacter G) = 0 := by
    have hh := hc₂ (trivialIrreducibleCharacter G); rw [htriv₂] at hh; exact_mod_cast hh.symm
  have hsymc₁ : ∀ χ, c₁ (IrreducibleCharacter.conjPerm G χ) = c₁ χ := fun χ => by
    have hh := ((hc₁ (IrreducibleCharacter.conjPerm G χ)).symm.trans (hsym₁ χ)).trans (hc₁ χ)
    exact_mod_cast hh
  have hsymc₂ : ∀ χ, c₂ (IrreducibleCharacter.conjPerm G χ) = c₂ χ := fun χ => by
    have hh := ((hc₂ (IrreducibleCharacter.conjPerm G χ)).symm.trans (hsym₂ χ)).trans (hc₂ χ)
    exact_mod_cast hh
  have htrivfix : IrreducibleCharacter.conjPerm G (trivialIrreducibleCharacter G)
      = trivialIrreducibleCharacter G :=
    (IrreducibleCharacter.conjPerm_eq_self_iff (trivialIrreducibleCharacter G)).mpr (by simp)
  rw [← Finset.add_sum_erase Finset.univ (fun χ => c₁ χ * c₂ χ)
      (Finset.mem_univ (trivialIrreducibleCharacter G)),
    hc2t, mul_zero, zero_add]
  refine even_sum_of_involution (fun χ _ => IrreducibleCharacter.conjPerm G χ)
    (fun χ hχ => ?_) (fun χ hχ => ?_) (fun χ _ => (IrreducibleCharacter.conjPerm G).left_inv χ)
    (fun χ _ => by rw [hsymc₁, hsymc₂])
  · rw [Finset.mem_erase] at hχ ⊢
    refine ⟨fun h => hχ.1 ?_, Finset.mem_univ _⟩
    exact (IrreducibleCharacter.conjPerm G).injective (h.trans htrivfix.symm)
  · rw [Finset.mem_erase] at hχ
    intro h
    exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hodd hχ.1
      ((IrreducibleCharacter.conjPerm_eq_self_iff χ).mp h)

open scoped Classical FiniteInduce in
/-- **The `σ`-column sum `∑_r ω_{r0}^σ` is real** (Peterfalvi (3.9)(a)).  The column-`0` `σ`-images
are permuted by the row-conjugation involution `σ` (`exists_rowInv_alignedOmegaSigma_conj`:
`conj ω_{r0}^σ = ω_{σr,0}^σ`), so the sum is conjugation-invariant.  This is the `M`-side reality
feeding the (11.8.5) `a = ⟨∑ω_{r0}^σ, β⟩` parity (`even_inner_of_conjPerm_symmetric`). -/
theorem Hypothesis.sum_alignedOmegaSigma_zeroColumn_isReal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    ClassFunction.IsReal (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) := by
  have := hyp.finiteG
  classical
  choose σ hσ using fun i => hyp.exists_rowInv_alignedOmegaSigma_conj hG hodd i
  have hbridge : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hgridinj : ∀ a b : Fin hyp.w1,
      hyp.alignedOmegaSigmaGrid hG hodd a 0 = hyp.alignedOmegaSigmaGrid hG hodd b 0 → a = b := by
    intro a b hab
    by_contra hne
    have hii := hyp.alignedOmegaSigmaGrid_inner hG hodd a b 0 0
    rw [← hab, hyp.alignedOmegaSigmaGrid_inner hG hodd a a 0 0, if_pos ⟨rfl, rfl⟩,
      if_neg (fun h => hne h.1)] at hii
    exact one_ne_zero hii
  have hσinv : Function.Involutive σ := fun r => by
    apply hgridinj
    calc hyp.alignedOmegaSigmaGrid hG hodd (σ (σ r)) 0
        = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (hyp.alignedOmegaSigmaGrid hG hodd (σ r) 0) := ((hσ (σ r)).1).symm
      _ = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
              (hyp.alignedOmegaSigmaGrid hG hodd r 0)) := by rw [(hσ r).1]
      _ = hyp.alignedOmegaSigmaGrid hG hodd r 0 := by
            rw [← hbridge, ← hbridge, ClassFunction.conj_conj]
  have hconjsum : ∀ s : Finset (Fin hyp.w1),
      (∑ r ∈ s, hyp.alignedOmegaSigmaGrid hG hodd r 0).conj
        = ∑ r ∈ s, (hyp.alignedOmegaSigmaGrid hG hodd r 0).conj := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, ClassFunction.conj_add, ih, Finset.sum_insert ha]
  rw [ClassFunction.IsReal, hconjsum Finset.univ,
    show (∑ r : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hodd r 0).conj)
        = ∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd (σ r) 0 from
      Finset.sum_congr rfl fun r _ => by rw [hbridge]; exact (hσ r).1]
  exact Equiv.sum_comp (Equiv.ofBijective σ hσinv.bijective)
    (fun r => hyp.alignedOmegaSigmaGrid hG hodd r 0)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), the "`a` even" step** (assembled).  If `a = ⟨∑_r ω_{r0}^σ, β⟩` with `β` a
real virtual character orthogonal to `1_G` (Peterfalvi (11.8.3): `β` is `i,j`-independent and real),
then `a` is even.  Both factors are real (`∑ω_{r0}^σ` via `sum_alignedOmegaSigma_zeroColumn_isReal`,
`β` by hypothesis) and lie in `ℤ[Irr G]`, and `β ⊥ 1`, so `even_inner_of_conjPerm_symmetric` gives
the parity.  This excludes `a = 1` (odd), so with `a ∈ {0,1,2}` (11.8.2) it forces `a ∈ {0,2}`, the
input to `charParam_a_eq_zero_of_residualEq`. -/
theorem Hypothesis.a_even_of_eq_inner_sumOmegaSigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {β : ClassFunction G ℂ} (hβZ : β ∈ ZIrr G)
    (hβr : ClassFunction.IsReal β)
    (hβ1 : ClassFunction.inner β (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0)
    {a : ℤ} (ha : (a : ℂ)
      = ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) β) :
    Even a := by
  have := hyp.finiteG
  have hωZ : (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) ∈ ZIrr G :=
    Submodule.sum_mem _ fun r _ => hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hodd r 0
  have hωr := hyp.sum_alignedOmegaSigma_zeroColumn_isReal hG hodd
  obtain ⟨z, hz, hev⟩ := even_inner_of_conjPerm_symmetric hodd hωZ hβZ hωr hβr hβ1
  have haz : a = z := by
    have hcast : (a : ℂ) = (z : ℂ) := ha.trans hz
    exact_mod_cast hcast
  rw [haz]; exact hev

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), `β ⊥ 1_G`** (`i ≠ 0`): `⟨α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁},
1_G⟩ = 0`.  Via the Dade adjoint `tau_inner_trivial` (`⟨α_{ij}^τ, 1_G⟩ = ⟨α_{ij}, 1_M⟩ =
0`, `hα1M`);
`1_G = ω_{00}^σ` (`alignedOmegaSigmaGrid_zero_zero`), so `⟨ω_{ij}^σ − ω_{i0}^σ, 1_G⟩ = 0`
(`alignedOmegaSigmaGrid_inner`, using `i ≠ 0`); and `⟨ζ^{τ₁}, 1_G⟩ = 0`
(Peterfalvi (5.3.b), `SHC_extension_inner_alignedOmegaSigma_eq_zero`).  This is the `β ⊥ 1` input to
the `a`-even parity `a_even_of_eq_inner_sumOmegaSigma`. -/
theorem Hypothesis.beta_inner_trivial [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (hi0 : i ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hα1M : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      (trivialClassFunction ↥M) = 0) :
    ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ)
      (trivialClassFunction G) = 0 := by
  have hsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hατ1 : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (trivialClassFunction G) = 0 := by
    rw [hyp.tau_inner_trivial hsupp]; exact hα1M
  have hωdiff1 : ClassFunction.inner
      (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
      (trivialClassFunction G) = 0 := by
    rw [← hyp.alignedOmegaSigmaGrid_zero_zero hG hodd, ClassFunction.inner_sub_left,
      hyp.alignedOmegaSigmaGrid_inner hG hodd i 0 j 0,
      hyp.alignedOmegaSigmaGrid_inner hG hodd i 0 0 0,
      if_neg (fun h => hi0 h.1), if_neg (fun h => hi0 h.1), sub_zero]
  have hζτ1 : ClassFunction.inner (coh.extension ζ)
      (trivialClassFunction G) = 0 := by
    rw [← hyp.alignedOmegaSigmaGrid_zero_zero hG hodd]
    exact hyp.SHC_extension_inner_alignedOmegaSigma_eq_zero hG coh hodd hζS hζirr hζ1 hζne 0 0
  rw [ClassFunction.inner_add_left, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    ClassFunction.inner_smul_left, hατ1, hωdiff1, hζτ1, mul_zero, mul_zero, sub_zero, add_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), `β ∈ ℤ[Irr G]`**: the (11.8.3) residual `β = α_{ij}^τ − δ(ω_{ij}^σ −
ω_{i0}^σ) + nζ^{τ₁}` is a virtual character.  `α_{ij}^τ ∈ ZIrr` (`muGridAlpha_tau_mem_ZIrr`), the
aligned `σ`-grid entries `∈ ZIrr` (`alignedOmegaSigmaGrid_mem_ZIrr`), and `ζ^{τ₁} ∈ ZIrr`
(`SHC_isCoherent.extension_mem_ZIrr`); `ZIrr G` is closed under `ℤ`/`ℕ`-linear combinations. -/
theorem Hypothesis.beta_mem_ZIrr [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ) :
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ) ∈ ZIrr G := by
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hζτZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have hωZ : (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
      ∈ ZIrr G :=
    Submodule.sub_mem _ (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hodd i j)
      (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hodd i 0)
  refine Submodule.add_mem _ (Submodule.sub_mem _ hαZ ?_) ?_
  · rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem hωZ δ
  · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hζτZ n

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), `⟨α_{ij}, 1_M⟩ = 0` for `i ≠ 0`**: the pre-Dade residual
`α_{ij} = μ_{ij} − δμ_{i0} − nζ` is orthogonal to the principal character of `M`.  The principal
character sits at the grid origin `μ_{00} = 1_M` (`muGrid_zero_zero_eq_trivial`), so for `i ≠ 0`,
`j ≠ 0` all three constituents avoid it: `⟨μ_{ij}, 1_M⟩ = ⟨μ_{ij}, μ_{00}⟩ = 0` (cross-column,
`j ≠ 0`), `⟨μ_{i0}, 1_M⟩ = ⟨μ_{i0}, μ_{00}⟩ = 0` (within-column, `i ≠ 0`), and `⟨ζ, 1_M⟩ = 0`
(`ζ(1) = w₁ > 1 ≠ 1`).  This discharges the `hα1M` hypothesis of `beta_inner_trivial`, making
`β ⊥ 1_G` unconditional for `i ≠ 0`. -/
theorem Hypothesis.muGridAlpha_inner_trivial_M [Finite G] {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i : Fin hyp.w1} (hi0 : i ≠ 0) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    {δ : ℤ} {n : ℕ} :
    ClassFunction.inner
        (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (trivialClassFunction (↥M)) = 0 := by
  have hμij : ClassFunction.inner (hyp.muGrid hG hodd i j) (trivialClassFunction (↥M)) = 0 := by
    rw [← hyp.muGrid_zero_zero_eq_trivial hG hodd]
    exact hyp.muGrid_inner_cross_column hG hodd i 0 hj0
  have hμi0 : ClassFunction.inner (hyp.muGrid hG hodd i 0) (trivialClassFunction (↥M)) = 0 := by
    rw [← hyp.muGrid_zero_zero_eq_trivial hG hodd]
    exact hyp.muGrid_inner_within_column hG hodd 0 hi0
  have hζ : ClassFunction.inner ζ (trivialClassFunction (↥M)) = 0 := by
    have hzmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζirr
    have htmem : trivialClassFunction (↥M) ∈ irreducibleCharacters (↥M) :=
      mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible
    rw [irr_cf_inner hzmem htmem, if_neg ?_]
    intro hcontra
    have h1 : ζ 1 = trivialClassFunction (↥M) 1 :=
      congrArg (fun f : ClassFunction (↥M) ℂ => (f : (↥M) → ℂ) 1) hcontra
    rw [hζ1, trivialClassFunction_apply] at h1
    have hw1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast h1
    omega
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, hμij, hμi0, hζ,
    mul_zero, mul_zero, sub_zero, sub_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), the parity anchor `a = (∑_r ω_{r0}^σ, β)`**: the residual coefficient `a`
(defined by `(α_{ij}^τ, ζ^{τ₁}) = a − n`, `hinner`) equals the `σ`-grid inner product of the
(11.8.3)
residual `β = α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁}`.  This is the identity feeding the parity
assembly `a_even_of_eq_inner_sumOmegaSigma` (β real virtual character ⊥ 1 ⇒ `a` even), the input
that excludes `a = 1` unconditionally.  Computation: `(α_{ij}^τ, ∑_r ω_{r0}^σ) = a − δ` (from
`muGridAlpha_tau_inner_zeroColumnSum_sub_zeta` `= n − δ`, the (11.8.4) rewrite `h114`, and
`hinner`);
`(ω^σ diff, ∑ω) = −1` (`alignedOmegaSigma_diff_inner_zeroColumnSum`); `(ζ^{τ₁}, ∑ω) = 0`
(`SHC_extension_inner_zeroColumnOmegaSigma_sum`, (5.3.b)) — so `(β, ∑ω) = (a − δ) − δ·(−1) + 0 = a`,
and conjugate-symmetry gives `(∑ω, β) = a`.  The `δ` in `β`'s coefficient cancels the `δ` from the
`α^τ` term, so this holds for **all** `δ` (not only `δ = 1`). -/
theorem Hypothesis.muGridAlpha_a_eq_inner_sumOmegaSigma_beta [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) {a : ℤ}
    (hinner : ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ))
    (h114 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - coh.extension ζ) :
    (a : ℂ) = ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
              - hyp.alignedOmegaSigmaGrid hG hodd i 0)
          + (n : ℂ) • coh.extension ζ) := by
  have hαω : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (a : ℂ) - (δ : ℂ) := by
    have h := hyp.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta hG hodd i hj0 hζS hζirr hζ1 hdeg hμ0
      hnf hδj hdζ h0ζ
    rw [h114, ClassFunction.inner_sub_right, hinner] at h
    linear_combination h
  have hβω : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (a : ℂ) := by
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left, hαω,
      hyp.alignedOmegaSigma_diff_inner_zeroColumnSum hG hodd i hj0,
      hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG coh hodd hζS hζirr hζ1 hζne]
    ring
  rw [OddOrder.RepresentationTheory.inner_conj_symm, hβω, star_intCast]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), `a = 0` under the (11.8.4) hypothesis** (the residual-orthogonal case).
Given the (11.8.4) by-contradiction consequence `(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − ζ^{τ₁}`
(`μ₀ = ∑ μ_{i'0}`),
the two-way computation of `(α_{ij}^τ, (μ₀ − ζ)^τ)` forces `a = 0` when `a ∈ {0, 2}`:
* `M`-side (via the Dade isometry, `muGridAlpha_tau_inner_zeroColumnSum_sub_zeta`): `= n − δ`;
* `G`-side (via (11.8.4) + the residual decomposition `α_{ij}^τ = δ(ω^σ diff) − nζ^{τ₁} + a∑β`
  for `a ∈ {0, 2}`, `SHC_residual_eq_omegaSigma_diff`, with `(ω^σ diff, ∑ω_{r0}^σ) = −1`
  (`alignedOmegaSigma_diff_inner_zeroColumnSum`) and the (5.3.b) orthogonalities
  `(ζ^{τ₁}, ∑ω) = (∑β, ∑ω) = 0`): `= −δ − (a − n) = n − δ − a`.
Equating gives `a = 0`.  With the parity `a` even (Peterfalvi (11.8.3), `β` real, excluding `a = 1`)
this is the full (11.8.5): under the residual-orthogonality assumption every column coefficient
`a = 0`, the key input to (11.8.6)'s `μ_j^{τ₂} = ∑ ω_{ij}^σ` coherence contradiction. -/
theorem Hypothesis.charParam_a_eq_zero_of_residualEq [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (h114 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - coh.extension ζ) :
    ∃ a : ℤ, (a = 0 ∨ a = 1 ∨ a = 2) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) ∧
      (Even a → a = 0) := by
  obtain ⟨a, Y, hbound, hinner, hYeq, hdecompA⟩ :=
    hyp.SHC_residual_eq_omegaSigma_diff hG coh hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf
      hδj hdζ h0ζ hδpm
      hn2 hRn hZ horth hRmem hRrev
  refine ⟨a, hbound, hinner, ?_⟩
  intro heven
  -- `a` even and `a ∈ {0,1,2}` gives `a ∈ {0,2}` (Peterfalvi (11.8.3)/(11.8.5): the parity `a` even
  -- from `β` real excludes `a = 1`).
  have ha02 : a = 0 ∨ a = 2 := by
    rcases hbound with h | h | h
    · exact Or.inl h
    · obtain ⟨k, hk⟩ := heven; omega
    · exact Or.inr h
  have hζne := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hYd := hYeq ha02
  have htrans := hyp.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta hG hodd i hj0 hζS hζirr hζ1
    hdeg hμ0 hnf hδj hdζ h0ζ
  rw [h114] at htrans
  have hαω : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = -(δ : ℂ) := by
    rw [hdecompA, hYd]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left,
      hyp.alignedOmegaSigma_diff_inner_zeroColumnSum hG hodd i hj0,
      hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG coh hodd hζS hζirr hζ1 hζne,
      hyp.R_sum_inner_zeroColumnOmegaSigma_sum hG coh hodd hRrev]
    ring
  rw [ClassFunction.inner_sub_right, hαω, hinner] at htrans
  have ha0 : (a : ℂ) = 0 := by linear_combination -htrans
  exact_mod_cast ha0

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5), unconditional `a = 0`**.  Combines the conditional (11.8.5)
`charParam_a_eq_zero_of_residualEq` (which gives `a ∈ {0,1,2}` and the implication
`Even a → a = 0`) with the parity assembly: the (11.8.3) residual
`β = α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁}` is a virtual character (`beta_mem_ZIrr`)
orthogonal
to `1_G` (`beta_inner_trivial`, its `hα1M` discharged by `muGridAlpha_inner_trivial_M` for `i ≠ 0`),
**real** (`beta_isReal`, the (11.8.3) reality), and `a = (∑_r ω_{r0}^σ, β)`
(`muGridAlpha_a_eq_inner_sumOmegaSigma_beta`); so `a` is even
(`a_even_of_eq_inner_sumOmegaSigma`, the general reality-parity of an integer inner product of
real virtual characters one of which is `⊥ 1_G` in odd order), which excludes `a = 1`.  Hence
`a = 0` unconditionally, i.e. `(α_{ij}^τ, ζ^{τ₁}) = −n`.  This is the full (11.8.5).

The formerly-threaded row-`0` (4.8)/(4.10) Dade identities `h48`/`h410` are now **discharged**
from the §10 instantiation of Hypothesis (4.6) (`tau_muGrid_zeroRow_diff` /
`tau_muGrid_fourCorner` via `toHypothesis46`, issue 9004); the residual input is the
`w₂`-primality `hw2` they need for the (10.3) cross-column degree constancy. -/
theorem Hypothesis.residualCoeff_eq_zero [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hconj : ∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M → IsIrreducibleCharacter χ →
      χ 1 = (hyp.w1 : ℂ) → (coh.extension χ).conj = coh.extension χ.conj)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (hi0 : i ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ} (hw2 : (hyp.w2).Prime)
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n) (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (h114 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - coh.extension ζ) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = -(n : ℂ) := by
  -- the (4.8)/(4.10) Dade identities, discharged from the §10 instantiation of (4.6)
  have hdeg0 : hyp.muGrid hG hodd 0 j 1 = (d : ℂ) :=
    (hyp.muGrid_apply_one_eq hG hodd hw2 0 i hj0 hj0).trans hdeg
  have h410 : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
        - (δ : ℂ) • hyp.muGrid hG hodd i 0 + (δ : ℂ) • hyp.muGrid hG hodd 0 0)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd 0 j
        - hyp.alignedOmegaSigmaGrid hG hodd i 0 + hyp.alignedOmegaSigmaGrid hG hodd 0 0) := by
    have := hyp.tau_muGrid_fourCorner hG hodd i j
    rwa [hδj] at this
  have h48 : ∀ k : Fin hyp.w2, k ≠ 0 →
      hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
        = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j
            - hyp.alignedOmegaSigmaGrid hG hodd 0 k) := fun k hk => by
    have := hyp.tau_muGrid_zeroRow_diff hG hodd hw2 hj0 hk
    rwa [hδj] at this
  have hβr := hyp.beta_isReal hG coh hconj hodd i hj0 hζS hζirr hζ1 hdeg0
    (hyp.muGrid_zero_column_apply_one hG hodd 0) hnf hδj h410 h48
  obtain ⟨a, hbound, hinner, heven_imp⟩ := hyp.charParam_a_eq_zero_of_residualEq hG coh hodd i
    hj0 hζS
    hζirr hζ1 hdeg hμ0 hnf hδj hdζ h0ζ hδpm hn2 hRn hZ horth hRmem hRrev h114
  have hζne := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have ha := hyp.muGridAlpha_a_eq_inner_sumOmegaSigma_beta hG coh hodd i hj0 hζS hζirr hζ1
    hζne hdeg hμ0
    hnf hδj hdζ h0ζ hinner h114
  have hβZ := hyp.beta_mem_ZIrr hG coh hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf hδj
  have hβ1 : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ)
      (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 :=
    hyp.beta_inner_trivial hG coh hodd i hj0 hi0 hζS hζirr hζ1 hζne hdeg hμ0 hnf hδj
      (hyp.muGridAlpha_inner_trivial_M hG hodd hi0 hj0 hζirr hζ1)
  have heven := hyp.a_even_of_eq_inner_sumOmegaSigma hG hodd hβZ hβr hβ1 ha
  have ha0 : a = 0 := heven_imp heven
  rw [ha0] at hinner
  rw [hinner]; ring

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.6) opening identity** `(μ_j − dζ)^τ = ∑_i ω_{ij}^σ − dζ^{τ₁}` (`0 < j`,
`δ = 1`).
Given the `a = 0` Dade images `α_{ij}^τ = ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}` for all `i` (`halpha`,
Peterfalvi (11.8.2)+(11.8.5), `SHC_tau_muGridAlpha_eq` at `δ = 1`) and the (11.8.4) value
`(μ₀ − ζ)^τ = ∑_i ω_{i0}^σ − ζ^{τ₁}` (`h114`), the `M`-level identity
`μ_j − dζ = (μ₀ − ζ) + ∑_i α_{ij}`
(needs `d = w₁·n + 1`, i.e. `δ = 1`) maps through the linear Dade isometry `τ` (`map_add`,
`map_sum`)
to `∑_i ω_{i0}^σ − ζ^{τ₁} + ∑_i (ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}) = ∑_i ω_{ij}^σ − dζ^{τ₁}`. This is
the
key step of (11.8.6): with `μ_j^{τ₂} = ∑_i ω_{ij}^σ` (via (4.9)/(5.8)) it makes `S(C) = S₁ ∪ S₂`
coherent, contradicting (11.3). -/
theorem Hypothesis.tau_muColumnSum_sub_zeta_eq_of_alphaImage [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (j : Fin hyp.w2) {ζ : ClassFunction ↥M ℂ} {d n : ℕ} (hd : (d : ℂ) = (hyp.w1 : ℂ) * (n : ℂ) + 1)
    (halpha : ∀ i : Fin hyp.w1,
      hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0
          - (n : ℂ) • coh.extension ζ)
    (h114 : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
          - coh.extension ζ) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        - (d : ℂ) • coh.extension ζ := by
  have hMlevel : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
      = ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        + ∑ i : Fin hyp.w1, (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) := by
    have hαe : (∑ i : Fin hyp.w1, (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        = (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0)
          - ((hyp.w1 : ℂ) * (n : ℂ)) • ζ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul, mul_comm]
    rw [hαe, hd]; module
  rw [hMlevel, map_add, h114, map_sum, Finset.sum_congr rfl (fun i _ => halpha i)]
  have hsum : (∑ i : Fin hyp.w1, (hyp.alignedOmegaSigmaGrid hG hodd i j
        - hyp.alignedOmegaSigmaGrid hG hodd i 0
        - (n : ℂ) • coh.extension ζ))
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        - (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - ((hyp.w1 : ℂ) * (n : ℂ)) • coh.extension ζ := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul, mul_comm]
  rw [hsum, hd]; module

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.5)+(11.8.6 opening), the assembled column identity**
`(μ_j − dζ)^τ = ∑_i ω_{ij}^σ − dζ^{τ₁}` (`0 < j`, `δ = 1`).  Assembles the (11.8.5) `a = 0` residual
coefficient into the full column Dade image: for every row `i ≠ 0`, `residualCoeff_eq_zero` gives
`(α_{ij}^τ, ζ^{τ₁}) = −n`, whence `SHC_tau_muGridAlpha_eq` gives the image
`α_{ij}^τ = ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}`; the `i = 0` image follows from any `i ≠ 0` one via the
four-corner (4.10) identity `tau_muGrid_fourCorner` (the `nζ` cancels in `α_{ij} − α_{0j}`, and
`μ_{0j} − μ_{00} − nζ = (α_{ij}) − (μ_{ij} − μ_{0j} − μ_{i0} + μ_{00})`).  With `δ = 1`
(`d = w₁·n + 1`) the (11.8.6) opening `tau_muColumnSum_sub_zeta_eq_of_alphaImage` then linearly
assembles the column sum.  The `S(HC)`-coherent extension `coh` and its orthonormal image data `R`
(`= coh.extension '' S(HC)`, `|R| = n`) are the (11.8.1)/(5.7) inputs; `h114` is the (11.8.4)
normalization; `δ = 1`, `n`, and the `R` cardinality `|S(HC)| = n` are the §9 (11.8.1) counts. -/
theorem Hypothesis.tau_muColumnSum_sub_dzeta_eq_of_residualData [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hconj : ∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M → IsIrreducibleCharacter χ →
      χ 1 = (hyp.w1 : ℂ) → (coh.extension χ).conj = coh.extension χ.conj)
    (hodd : Odd (Nat.card G)) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d n : ℕ} (hw2 : (hyp.w2).Prime)
    (hd : (d : ℂ) = (hyp.w1 : ℂ) * (n : ℂ) + 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - 1)
    (hdegall : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0all : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 1 = 1)
    (hδj : hyp.muColumnSign hG hodd j = 1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n) (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ)
    (h114 : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) - coh.extension ζ) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        - (d : ℂ) • coh.extension ζ := by
  have hw1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hdℕ : d = hyp.w1 * n + 1 := by exact_mod_cast hd
  have hw1le : hyp.w1 ≤ hyp.w1 * n := Nat.le_mul_of_pos_right _ (by omega)
  have hdgt : hyp.w1 < d := by omega
  have hζne : ζ.conj ≠ ζ := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hdζall : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i j 1 ≠ ζ 1 := fun i => by
    rw [hdegall i, hζ1]; exact_mod_cast (by omega : d ≠ hyp.w1)
  have h0ζall : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 1 ≠ ζ 1 := fun i => by
    rw [hμ0all i, hζ1]; exact_mod_cast (by omega : (1 : ℕ) ≠ hyp.w1)
  -- the row-`i` Dade image `α_{ij}^τ = ω_{ij}^σ − ω_{i0}^σ − nζ^{τ₁}` for `i ≠ 0`
  have halpha_ne : ∀ i : Fin hyp.w1, i ≠ 0 →
      hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0
          - (n : ℂ) • coh.extension ζ := by
    intro i hi0
    have hα0 := hyp.residualCoeff_eq_zero hG coh hconj hodd i hj0 hi0 hζS hζirr hζ1 hw2
      (hdegall i) (hμ0all i) hnf hδj (hdζall i) (h0ζall i) (Or.inl rfl) hn2 hRn hZ horth hRmem hRrev
      h114
    have himg := hyp.SHC_tau_muGridAlpha_eq hG coh hodd i hj0 hζS hζirr hζ1 hζne (hdegall i)
      (hμ0all i) hnf hδj (hdζall i) (h0ζall i) (Or.inl rfl) hα0
    simpa only [Int.cast_one, one_smul] using himg
  -- the row-`0` image via the four-corner identity from row `i₁ = 1 ≠ 0`
  have halpha : ∀ i : Fin hyp.w1,
      hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0
          - (n : ℂ) • coh.extension ζ := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      set i₁ : Fin hyp.w1 := ⟨1, by omega⟩ with hi1def
      have hi1 : i₁ ≠ 0 := by rw [hi1def]; simp [Fin.ext_iff]
      have h410 := hyp.tau_muGrid_fourCorner hG hodd i₁ j
      rw [hδj] at h410
      simp only [Int.cast_one, one_smul] at h410
      have key : hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ
          = (hyp.muGrid hG hodd i₁ j - hyp.muGrid hG hodd i₁ 0 - (n : ℂ) • ζ)
            - (hyp.muGrid hG hodd i₁ j - hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd i₁ 0
                + hyp.muGrid hG hodd 0 0) := by module
      rw [key, map_sub, halpha_ne i₁ hi1, h410]; module
    · exact halpha_ne i hi0
  exact hyp.tau_muColumnSum_sub_zeta_eq_of_alphaImage hG hodd coh j hd halpha h114

open scoped Classical FiniteInduce in
/-- **The orthonormal coherent image `R = coh.extension '' S(HC)`** (Peterfalvi (11.8.1)/(5.7)):
the image of the degree-`w₁` irreducible subfamily `S(HC)` under an `S(HC)`-coherent extension `coh`
is a Finset of mutually orthonormal virtual characters in `ℤ[Irr G]`.  The `extension` isometry
(`extension_inner_eq`) carries the orthonormal irreducibles of `S(HC)` (`irr_cf_inner`) to an
orthonormal set — also giving injectivity, so `|R| = |S(HC)|` — and lands them in `ℤ[Irr G]`
(`extension_mem_ZIrr`).  This materializes the `R` data (`hZ`/`horth`/`hRmem`/`hRrev`) the (11.8.5)
`residualCoeff_eq_zero`/`tau_muColumnSum_sub_dzeta_eq_of_residualData` consume; only the cardinality
value `|S(HC)| = n` remains the §9 (11.8.1) count (`caseB_degree_qu` + Frobenius `(u−1)/q`). -/
theorem Hypothesis.exists_coherentImage_SHC [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) :
    ∃ R : Finset (ClassFunction G ℂ),
      (∀ β ∈ R, β ∈ ZIrr G) ∧
      (∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0) ∧
      (∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
        φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R) ∧
      (∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ,
        φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) ∧
      R.card = (Finset.univ.filter (fun χ : IrreducibleCharacter ↥M =>
        (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
          ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ))).card := by
  have := hyp.finiteG
  classical
  set p : IrreducibleCharacter ↥M → Prop := fun χ =>
    (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
      ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ) with hp
  set s : Finset (IrreducibleCharacter ↥M) := Finset.univ.filter p with hs_def
  have hmem_s : ∀ χ, χ ∈ s ↔ p χ := fun χ => by
    rw [hs_def, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)
  -- each `χ ∈ s` is a member of `S(HC) = SHCSet`, hence lies in `zSpan SHCSet`
  have hspan : ∀ χ : IrreducibleCharacter ↥M, χ ∈ s →
      (χ : ClassFunction ↥M ℂ) ∈ OddOrder.Peterfalvi.S07.zSpan hyp.SHCSet := fun χ hχ =>
    Submodule.subset_span ⟨((hmem_s χ).mp hχ).1, χ.2, ((hmem_s χ).mp hχ).2⟩
  set f : IrreducibleCharacter ↥M → ClassFunction G ℂ :=
    fun χ => coh.extension (χ : ClassFunction ↥M ℂ) with hf
  -- the extension isometry carries the orthonormal `χ ∈ s` to an orthonormal image
  have hiso : ∀ χ χ' : IrreducibleCharacter ↥M, χ ∈ s → χ' ∈ s →
      ClassFunction.inner (f χ) (f χ') = if χ = χ' then (1 : ℂ) else 0 := by
    intro χ χ' hχ hχ'
    rw [hf, coh.extension_inner_eq _ _ (hspan χ hχ) (hspan χ' hχ'),
      irr_cf_inner (mem_irreducibleCharacters.mpr χ.2) (mem_irreducibleCharacters.mpr χ'.2)]
    simp only [Subtype.coe_inj]
  have hinjOn : ∀ χ ∈ s, ∀ χ' ∈ s, f χ = f χ' → χ = χ' := by
    intro χ hχ χ' hχ' hfeq
    by_contra hne
    have h1 : ClassFunction.inner (f χ) (f χ') = 0 := by rw [hiso χ χ' hχ hχ', if_neg hne]
    have h2 : ClassFunction.inner (f χ) (f χ') = 1 := by
      rw [hfeq, hiso χ' χ' hχ' hχ', if_pos rfl]
    rw [h1] at h2; exact one_ne_zero h2.symm
  refine ⟨s.image f, ?_, ?_, ?_, ?_, ?_⟩
  · -- hZ
    intro β hβ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hβ
    exact coh.extension_mem_ZIrr _ (hspan χ hχ)
  · -- horth
    intro α hα β hβ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hα
    obtain ⟨χ', hχ', rfl⟩ := Finset.mem_image.mp hβ
    rw [hiso χ χ' hχ hχ']
    by_cases hc : χ = χ'
    · rw [if_pos hc, if_pos (by rw [hc])]
    · rw [if_neg hc, if_neg (fun h => hc (hinjOn χ hχ χ' hχ' h))]
  · -- hRmem
    intro φ hφS hφirr hφ1
    exact Finset.mem_image.mpr ⟨⟨φ, hφirr⟩, (hmem_s _).mpr ⟨hφS, hφ1⟩, rfl⟩
  · -- hRrev
    intro β hβ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hβ
    obtain ⟨hφS, hφ1⟩ := (hmem_s χ).mp hχ
    exact ⟨(χ : ClassFunction ↥M ℂ), hφS, χ.2, hφ1, rfl⟩
  · -- cardinality: injective on `s`
    exact Finset.card_image_of_injOn hinjOn

/-- **Peterfalvi (10.10.1), pure arithmetic**: for the type-V case (c) parameters — `p = w₂` prime,
`w₁ ∣ p+1` (both odd, `w₁ > 1`), and the Huppert bound `|H:H'| = p² ≤ 4w₁²+1` (6.5.a) — one has
`p = 2w₁ − 1`, hence `w₁ < p = w₂`.

Writing `p+1 = 2k·w₁` (`m := (p+1)/w₁` is even, since `p+1` is even and `w₁` odd), the bound gives
`(2kw₁−1)² ≤ 4w₁²+1`, i.e. `w₁(k²−1) ≤ k`; with `w₁ ≥ 2`, `k ≥ 1` this forces `k = 1`.  Mirrors the
`typeII_noncoherence_arithmetic` pattern (the analytic/structural inputs are isolated). -/
theorem typeV_param_arithmetic {p w₁ : ℕ} (hpodd : Odd p) (hw1odd : Odd w₁) (hw1 : 1 < w₁)
    (hdvd : w₁ ∣ p + 1) (hbound : p ^ 2 ≤ 4 * w₁ ^ 2 + 1) :
    p = 2 * w₁ - 1 ∧ w₁ < p := by
  obtain ⟨m, hm⟩ := hdvd
  -- `m` is even: `p+1` is even (`p` odd) and `w₁` is odd.
  have hm_even : Even m := by
    have hp1even : Even (p + 1) := Odd.add_one hpodd
    rw [hm] at hp1even
    rcases Nat.even_mul.mp hp1even with h | h
    · exact absurd h (Nat.not_even_iff_odd.mpr hw1odd)
    · exact h
  obtain ⟨k, hk⟩ := hm_even
  have hpk : p + 1 = 2 * w₁ * k := by rw [hm, hk]; ring
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h1
    · rw [h0, Nat.mul_zero] at hpk; omega
    · exact h1
  -- `k = 1` from the bound (over `ℤ` to avoid `ℕ`-subtraction).
  have hk1 : k = 1 := by
    have hpZ : (p : ℤ) = 2 * w₁ * k - 1 := by
      have : (p : ℤ) + 1 = 2 * (w₁ : ℤ) * k := by exact_mod_cast hpk
      linarith
    have hboundZ : (p : ℤ) ^ 2 ≤ 4 * (w₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hbound
    rw [hpZ] at hboundZ
    have hw1Z : (2 : ℤ) ≤ w₁ := by exact_mod_cast hw1
    have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast hkpos
    have hkle : (k : ℤ) ≤ 1 := by
      nlinarith [hboundZ, hw1Z, hkZ, mul_nonneg (by linarith : (0:ℤ) ≤ (w₁:ℤ) - 2)
        (by nlinarith : (0:ℤ) ≤ (k:ℤ)^2 - 1), sq_nonneg ((k:ℤ) - 1)]
    omega
  subst hk1
  constructor
  · omega
  · omega

end OddOrder.Peterfalvi.S12


