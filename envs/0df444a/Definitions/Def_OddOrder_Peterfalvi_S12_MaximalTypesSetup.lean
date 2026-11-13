-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_MaximalTypesSetup
-- name    : OddOrder_Peterfalvi_S12_MaximalTypesSetup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:23:53.142204+00:00
-- url     : https://prove2.me/theorems/9b03fda8-f130-4454-8110-0427a877d71c
-- title:
--   Peterfalvi §12: maximal types III, IV, V, opening layer
-- statement:
--   The opening layer of the (11.8.4) analysis for maximal subgroups of types III, IV and V: the dichotomy form for $\tau$ of the column-0 $\mu$-sum minus $\zeta$, and the branch-2 swap.
--
--   Main declarations: `Hypothesis.tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal` (Peterfalvi (11.8.4), dichotomy form); `Hypothesis.SHC_swap` (Peterfalvi (11.8.4), the branch-2 "we may assume" swap); `Hypothesis.SHC_swap_h114` (h114 for the branch-2 swap); `Hypothesis.SHC_swap_conj` (The branch-2 swap commutes with complex conjugation).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_MaximalTypesSetup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_MaximalTypesSetup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_Props109To1011

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), dichotomy form.**  Under the (11.8) contradiction hypothesis — the
residual `(μ₀ − ζ)^τ − ∑_r ω_{r0}^σ` is orthogonal to every `ω_{ij}^σ` — the Dade image
`(μ₀ − ζ)^τ` differs from `∑_r ω_{r0}^σ` by a **single signed coherent extension**: either
`(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − ζ^{τ₁}` (the normalized (11.8.4) form), or the degree-`w₁` family
`S₁ = S(HC)` is the bare conjugate pair `{ζ, ζ̄}` and `(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ + ζ̄^{τ₁}`.

Textbook proof (p. 66): write `(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − χ`.  The orthogonality hypothesis pins
`⟨(μ₀ − ζ)^τ, ω_{r0}^σ⟩ = 1`, so `‖χ‖² = ‖μ₀ − ζ‖² − w₁ = 1` (Dade isometry on the `A₀`-supported
lattice, `‖μ₀ − ζ‖² = w₁ + 1` from `inner_muColumnZero_sub_zeta_self`).  Computing
`⟨(μ₀ − ζ)^τ, (ζ − ζ̄)^τ⟩ = ⟨μ₀ − ζ, ζ − ζ̄⟩ = −1` against the supported split
`(ζ − ζ̄)^τ = ζ^{τ₁} − ζ̄^{τ₁}` and the (5.3.b) orthogonalities `⟨λ^{τ₁}, ∑_r ω_{r0}^σ⟩ = 0` gives
`⟨χ, ζ^{τ₁}⟩ − ⟨χ, ζ̄^{τ₁}⟩ = 1`, with both inner products integers (`ZIrr` pairing) of square
`≤ 1` (Cauchy–Schwarz in the unit-norm integral lattice), whence `⟨χ, ζ^{τ₁}⟩ = 1` (then
`χ = ζ^{τ₁}` by positive definiteness) or `⟨χ, ζ̄^{τ₁}⟩ = −1` (then `χ = −ζ̄^{τ₁}`).  In the second
case any third family member `λ ∈ S₁ − {ζ, ζ̄}` would give
`1 = ⟨μ₀ − ζ, λ − ζ⟩ = ⟨(μ₀ − ζ)^τ, λ^{τ₁} − ζ^{τ₁}⟩ = 0`, so `S₁ = {ζ, ζ̄}`.

The textbook's "we may assume" is the replacement of `τ₁` by its negated conjugate-swap
`λ ↦ −(λ̄)^{τ₁}` in the second branch — deferred to the consumer, since the swap is again a
coherent extension of `τ` on `ℤ[S₁]` precisely because `S₁ = {ζ, ζ̄}` (every `A₀`-supported lattice
element is then an integer multiple of `ζ − ζ̄`). -/
theorem Hypothesis.tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (horth : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
          - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0) :
    hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - (hyp.SHC_isCoherent hG).extension ζ
    ∨ ((∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
          lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj) ∧
        hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
          = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
            + (hyp.SHC_isCoherent hG).extension ζ.conj) := by
  have := hyp.finiteG
  classical
  have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  -- generic unit-norm integral-lattice toolkit: the Cauchy–Schwarz bound `m² ≤ 1` and the
  -- positive-definiteness equalities `⟨A, θ⟩ = ±1 → A = ±θ` for unit-norm `A`, `θ`.
  have hbound : ∀ (A θ : ClassFunction G ℂ) (m : ℤ),
      ClassFunction.inner A A = 1 → ClassFunction.inner A θ = (m : ℂ) →
      ClassFunction.inner θ θ = 1 → m * m ≤ 1 := by
    intro A θ m hA hm hθ
    have hθA : ClassFunction.inner θ A = (m : ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hm, star_intCast]
    have hval : ClassFunction.inner (A - (m : ℂ) • θ) (A - (m : ℂ) • θ)
        = ((1 - m * m : ℤ) : ℂ) := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, hA, hm, hθA, hθ,
        star_intCast]
      push_cast
      ring
    have hre := OddOrder.RepresentationTheory.inner_self_re_nonneg (A - (m : ℂ) • θ)
    rw [hval] at hre
    have h1 : (0 : ℝ) ≤ ((1 - m * m : ℤ) : ℝ) := by simpa using hre
    have h2 : (0 : ℤ) ≤ 1 - m * m := by exact_mod_cast h1
    linarith
  have heq : ∀ A θ : ClassFunction G ℂ, ClassFunction.inner A A = 1 →
      ClassFunction.inner A θ = 1 → ClassFunction.inner θ θ = 1 → A = θ := by
    intro A θ hA hAθ hθ
    have hθA : ClassFunction.inner θ A = 1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hAθ, star_one]
    have hz : ClassFunction.inner (A - θ) (A - θ) = 0 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hA, hAθ, hθA, hθ]
      ring
    have h0 : A - θ = 0 := by
      refine OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero ?_
      rw [hz]
      simp
    exact sub_eq_zero.mp h0
  have heqneg : ∀ A θ : ClassFunction G ℂ, ClassFunction.inner A A = 1 →
      ClassFunction.inner A θ = -1 → ClassFunction.inner θ θ = 1 → A = -θ := by
    intro A θ hA hAθ hθ
    have hθA : ClassFunction.inner θ A = -1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hAθ]
      simp
    have hz : ClassFunction.inner (A + θ) (A + θ) = 0 := by
      rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
        ClassFunction.inner_add_right, hA, hAθ, hθA, hθ]
      ring
    have h0 : A + θ = 0 := by
      refine OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero ?_
      rw [hz]
      simp
    exact add_eq_zero_iff_eq_neg.mp h0
  -- conjugate-family facts for `ζ`
  have hζne : ζ.conj ≠ ζ := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by
    rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have hζmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζirr
  have hζcmem : ζ.conj ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζcirr
  -- supports
  have hsupp : ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
  have hsuppd : (ζ - ζ.conj).support ⊆ hyp.A0 := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  -- `ψ = (μ₀ − ζ)^τ ∈ ZIrr G`
  have hμ0Z : (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun i _ => (hyp.muGrid_isIrreducible hG hodd i 0).mem_ZIrr)
  have hdiffZ : ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _ hμ0Z hζirr.mem_ZIrr
  have hψZ : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hsupp hdiffZ
  have heζZ : (hyp.SHC_isCoherent hG).extension ζ ∈ ZIrr G :=
    (hyp.SHC_isCoherent hG).extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have heζcZ : (hyp.SHC_isCoherent hG).extension ζ.conj ∈ ZIrr G :=
    (hyp.SHC_isCoherent hG).extension_mem_ZIrr ζ.conj
      (Submodule.subset_span ⟨hζcS, hζcirr, hζc1⟩)
  -- `M`-side orthogonality facts
  have hμζ : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ζ = 0 := by
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr ?_
    rw [hyp.muGrid_zero_column_apply_one hG hodd i, hζ1]
    intro he
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
    omega
  have hμζc : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) ζ.conj = 0 := by
    rw [inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζcirr ?_
    rw [hyp.muGrid_zero_column_apply_one hG hodd i, hζc1]
    intro he
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
    omega
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    rw [irr_cf_inner hζmem hζmem, if_pos rfl]
  have hζζc : ClassFunction.inner ζ ζ.conj = 0 := by
    rw [irr_cf_inner hζmem hζcmem, if_neg hζne.symm]
  -- `G`-side norm bookkeeping under the orthogonality hypothesis
  have hΩr : ∀ r : Fin hyp.w1,
      ClassFunction.inner (∑ r' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r' 0)
        (hyp.alignedOmegaSigmaGrid hG hodd r 0) = 1 := by
    intro r
    rw [inner_sum_left, Finset.sum_eq_single r]
    · rw [hyp.alignedOmegaSigmaGrid_inner hG hodd r r 0 0, if_pos ⟨rfl, rfl⟩]
    · intro r' _ hne
      rw [hyp.alignedOmegaSigmaGrid_inner hG hodd r' r 0 0, if_neg fun h => hne h.1]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hψr : ∀ r : Fin hyp.w1,
      ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hodd r 0) = 1 := by
    intro r
    have h := horth r 0
    rw [ClassFunction.inner_sub_left, sub_eq_zero] at h
    exact h.trans (hΩr r)
  have hψΩ : ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl fun r _ => hψr r, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hΩψ : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hψΩ, star_natCast]
  have hΩnorm : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl fun r _ => hΩr r, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hψnorm : ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = ((hyp.w1 + 1 : ℕ) : ℂ) := by
    rw [hyp.tau_inner_eq_of_supported hsupp hsupp]
    exact inner_muColumnZero_sub_zeta_self hG hyp hζirr hζ1
  -- `χ = ∑_r ω_{r0}^σ − (μ₀ − ζ)^τ` has norm `1`
  have hχnorm : ClassFunction.inner
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = 1 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hΩnorm, hΩψ, hψΩ, hψnorm]
    push_cast
    ring
  -- the (5.3.b) orthogonalities `⟨∑_r ω_{r0}^σ, λ^{τ₁}⟩ = 0`
  have heΩ : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 :=
    hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG (hyp.SHC_isCoherent hG) hodd
      hζS hζirr hζ1 hζne
  have hΩe : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      ((hyp.SHC_isCoherent hG).extension ζ) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, heΩ, star_zero]
  have hζcne : (ζ.conj).conj ≠ ζ.conj := by
    rw [ClassFunction.conj_conj]
    exact hζne.symm
  have heΩc : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
      (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 :=
    hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG (hyp.SHC_isCoherent hG) hodd
      hζcS hζcirr hζc1 hζcne
  have hΩec : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, heΩc, star_zero]
  -- the integer coefficients `s = ⟨ψ, ζ^{τ₁}⟩`, `t = ⟨ψ, ζ̄^{τ₁}⟩` with `s − t = −1`
  obtain ⟨s, hs⟩ := ClassFunction.inner_mem_ZIrr_int hψZ heζZ
  obtain ⟨t, ht⟩ := ClassFunction.inner_mem_ZIrr_int hψZ heζcZ
  have hGside : ClassFunction.inner
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (hyp.tau (ζ - ζ.conj)) = -1 := by
    rw [hyp.tau_inner_eq_of_supported hsupp hsuppd, ClassFunction.inner_sub_left,
      ClassFunction.inner_sub_right, ClassFunction.inner_sub_right, hμζ, hμζc, hζζ, hζζc]
    ring
  rw [hyp.tau_zeta_sub_conj_eq_SHC_extension hG (hyp.SHC_isCoherent hG) hodd hζS hζirr hζ1,
    ClassFunction.inner_sub_right, hs, ht] at hGside
  have hstz : s - t = -1 := by exact_mod_cast hGside
  -- Cauchy–Schwarz bounds and the integer dichotomy `s = −1 ∨ t = 1`
  have hee : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ)
      ((hyp.SHC_isCoherent hG).extension ζ) = 1 :=
    hyp.SHC_extension_inner_self hG (hyp.SHC_isCoherent hG) hζS hζirr hζ1
  have heec : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = 1 :=
    hyp.SHC_extension_inner_self hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1
  have hmA : ClassFunction.inner
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((hyp.SHC_isCoherent hG).extension ζ) = ((-s : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, hΩe, hs]
    push_cast
    ring
  have hmAc : ClassFunction.inner
      ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      ((hyp.SHC_isCoherent hG).extension ζ.conj) = ((-t : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, hΩec, ht]
    push_cast
    ring
  have hs2 : s * s ≤ 1 := by
    have h := hbound _ _ (-s) hχnorm hmA hee
    have h' : s * s = -s * -s := by ring
    rw [h']
    exact h
  have ht2 : t * t ≤ 1 := by
    have h := hbound _ _ (-t) hχnorm hmAc heec
    have h' : t * t = -t * -t := by ring
    rw [h']
    exact h
  have hsle : s ≤ 1 := by nlinarith [mul_self_nonneg (s - 1)]
  have hsge : -1 ≤ s := by nlinarith [mul_self_nonneg (s + 1)]
  have htle : t ≤ 1 := by nlinarith [mul_self_nonneg (t - 1)]
  have htge : -1 ≤ t := by nlinarith [mul_self_nonneg (t + 1)]
  have hcase : s = -1 ∨ t = 1 := by omega
  rcases hcase with hsval | htval
  · -- `⟨χ, ζ^{τ₁}⟩ = 1`: `χ = ζ^{τ₁}`, the normalized (11.8.4) form
    left
    have hAe : ClassFunction.inner
        ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        ((hyp.SHC_isCoherent hG).extension ζ) = 1 := by
      rw [ClassFunction.inner_sub_left, hΩe, hs, hsval]
      push_cast
      ring
    have hχe := heq _ _ hχnorm hAe hee
    rw [← hχe]
    abel
  · -- `⟨χ, ζ̄^{τ₁}⟩ = −1`: `χ = −ζ̄^{τ₁}` and `S₁ = {ζ, ζ̄}`
    right
    have hAec : ClassFunction.inner
        ((∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        ((hyp.SHC_isCoherent hG).extension ζ.conj) = -1 := by
      rw [ClassFunction.inner_sub_left, hΩec, ht, htval]
      push_cast
      ring
    have hχec := heqneg _ _ hχnorm hAec heec
    have hψeq : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          + (hyp.SHC_isCoherent hG).extension ζ.conj := by
      rw [sub_eq_iff_eq_add] at hχec
      rw [hχec]
      abel
    refine ⟨fun lam hlamS hlamirr hlam1 => ?_, hψeq⟩
    by_contra hboth
    rw [not_or] at hboth
    obtain ⟨hlamzeta, hlamzetac⟩ := hboth
    have hlamne : lam.conj ≠ lam := hyp.inducedFamily_degree_w1_conj_ne hG hlamirr hlam1
    have hmulam : ClassFunction.inner (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) lam = 0 := by
      rw [inner_sum_left]
      refine Finset.sum_eq_zero fun i _ => ?_
      refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hlamirr ?_
      rw [hyp.muGrid_zero_column_apply_one hG hodd i, hlam1]
      intro he
      have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
      omega
    have hlammem : lam ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hlamirr
    have hzetalam : ClassFunction.inner ζ lam = 0 := by
      rw [irr_cf_inner hζmem hlammem, if_neg (Ne.symm hlamzeta)]
    have hsupplam : (lam - ζ).support ⊆ hyp.A0 :=
      hyp.inducedFamily_sub_support hlamS hζS (by rw [hlam1, hζ1])
    have hGlam : ClassFunction.inner
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (hyp.tau (lam - ζ)) = 1 := by
      rw [hyp.tau_inner_eq_of_supported hsupp hsupplam, ClassFunction.inner_sub_left,
        ClassFunction.inner_sub_right, ClassFunction.inner_sub_right, hmulam, hμζ, hzetalam, hζζ]
      ring
    have hspanlam : lam ∈ OddOrder.Peterfalvi.S07.zSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
      Submodule.subset_span ⟨hlamS, hlamirr, hlam1⟩
    have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
      Submodule.subset_span ⟨hζS, hζirr, hζ1⟩
    have hmemsupp : (lam - ζ) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 :=
      ⟨Submodule.sub_mem _ hspanlam hspanζ, hsupplam⟩
    have htaulam : hyp.tau (lam - ζ) = (hyp.SHC_isCoherent hG).extension lam
        - (hyp.SHC_isCoherent hG).extension ζ := by
      rw [← (hyp.SHC_isCoherent hG).extends_on_supported _ hmemsupp, map_sub]
    have heOmegalam : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension lam)
        (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 :=
      hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG (hyp.SHC_isCoherent hG) hodd
        hlamS hlamirr hlam1 hlamne
    have hOmegalam : ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
        ((hyp.SHC_isCoherent hG).extension lam) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, heOmegalam, star_zero]
    have heclam : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
        ((hyp.SHC_isCoherent hG).extension lam) = 0 :=
      hyp.SHC_extension_inner_of_ne hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1
        hlamS hlamirr hlam1 (Ne.symm hlamzetac)
    have hece : ClassFunction.inner ((hyp.SHC_isCoherent hG).extension ζ.conj)
        ((hyp.SHC_isCoherent hG).extension ζ) = 0 :=
      hyp.SHC_extension_inner_of_ne hG (hyp.SHC_isCoherent hG) hζcS hζcirr hζc1 hζS hζirr hζ1 hζne
    rw [htaulam, ClassFunction.inner_sub_right, hψeq, ClassFunction.inner_add_left,
      ClassFunction.inner_add_left, hOmegalam, heclam, hΩe, hece] at hGlam
    norm_num at hGlam

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), the branch-2 "we may assume" swap.**  When the degree-`w₁` family
`S₁ = S(HC)` is the bare conjugate pair `{ζ, ζ̄}` (the second branch of
`tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal`), the map `φ ↦ −(ζ̄-side extension of φ̄)`, i.e.
`SHC_swap.extension φ = −(SHC_isCoherent.extension φ.conj)`, is again a **coherent extension of `τ`
to `ℤ[S(HC)]`** — the textbook's replacement of `ζ^{τ₁}, ζ̄^{τ₁}` by `−ζ̄^{τ₁}, −ζ^{τ₁}` (p. 66).

The four `IsCoherent` fields:
* **isometry on `ℤ[S(HC)]`**: `S(HC)` is closed under conjugation (`inducedFamily` is, degrees are
  preserved), so `φ̄, ψ̄ ∈ ℤ[S(HC)]`; `⟨SHC(φ̄), SHC(ψ̄)⟩ = ⟨φ̄, ψ̄⟩ = star⟨φ,ψ⟩ = ⟨φ,ψ⟩`
  (`inner_conj_conj` and the reality of a `ZIrr` pairing);
* **agrees with `τ` on `ℤ[S(HC), A₀]`**: this is where `S(HC) = {ζ, ζ̄}` is used — every
  `A₀`-supported element of `span{ζ, ζ̄}` is a multiple `a(ζ − ζ̄)` (value at `1` is `(a+b)w₁ = 0`),
  on which
  `SHC_swap` and `SHC` both send `ζ − ζ̄ ↦ ζ^{τ₁} − ζ̄^{τ₁} = τ(ζ − ζ̄)`;
* **maps into `ZIrr`** and **nonzero-supported witness `ζ − ζ̄`**: inherited from `SHC`.

Combined with the dichotomy this gives the h114-producing extension in *both* branches (branch 1:
`SHC_isCoherent`; branch 2: this swap), i.e. Peterfalvi's "we may assume `(μ₀−ζ)^τ = ∑ω − ζ^{τ₁}`"
holds for a canonical choice of coherent `τ₁`. -/
noncomputable def Hypothesis.SHC_swap [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (htwo : ∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
      lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 := by
  haveI := hyp.finiteG
  classical
  set SHCset : Set (ClassFunction ↥M ℂ) :=
    {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} with hSHCset
  -- the `ζ̄`-side degree-`w₁` conjugate facts
  have hζne : ζ.conj ≠ ζ := hyp.inducedFamily_degree_w1_conj_ne hG hζirr hζ1
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have hζmem : ζ ∈ SHCset := ⟨hζS, hζirr, hζ1⟩
  have hζcmem : ζ.conj ∈ SHCset := ⟨hζcS, hζcirr, hζc1⟩
  -- `SHCset` is closed under conjugation.
  have hconj_closed : ∀ φ ∈ SHCset, φ.conj ∈ SHCset := by
    rintro φ ⟨hφS, hφirr, hφ1⟩
    exact ⟨inducedFamily_closedUnderConjugate M hφS, hφirr.conj, by
      rw [ClassFunction.conj_apply, hφ1, star_natCast]⟩
  -- the swap extension `φ ↦ −SHC(φ̄)`, packaged as an integral character map.
  set ext' : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G :=
    -((hyp.SHC_isCoherent hG).extension.comp
      (ClassFunction.mapRingEquivLinear (G := ↥M) Complex.conjAe.toRingEquiv)) with hext'def
  have hconjbridge : ∀ φ : ClassFunction ↥M ℂ,
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ = φ.conj := fun φ => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hext'apply : ∀ φ : ClassFunction ↥M ℂ,
      ext' φ = -((hyp.SHC_isCoherent hG).extension φ.conj) := by
    intro φ
    rw [hext'def, LinearMap.neg_apply, LinearMap.comp_apply,
      ClassFunction.mapRingEquivLinear_apply, hconjbridge]
  have hconj_zsmul : ∀ (n : ℤ) (x : ClassFunction ↥M ℂ), (n • x).conj = n • x.conj := by
    intro n x
    rw [← hconjbridge (n • x), ClassFunction.mapRingEquiv_zsmul, hconjbridge x]
  -- span-level conjugation closure.
  have hspan_conj : ∀ φ : ClassFunction ↥M ℂ, φ ∈ OddOrder.Peterfalvi.S07.zSpan SHCset →
      φ.conj ∈ OddOrder.Peterfalvi.S07.zSpan SHCset := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hconj_closed x hx)
    | zero => rw [ClassFunction.conj_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [ClassFunction.conj_add]; exact Submodule.add_mem _ hx hy
    | smul n x _ hx => rw [hconj_zsmul]; exact Submodule.smul_mem _ n hx
  -- span elements are `ZIrr`-members (so pairings are integers, hence real).
  have hspan_ZIrr : ∀ φ : ClassFunction ↥M ℂ, φ ∈ OddOrder.Peterfalvi.S07.zSpan SHCset →
      φ ∈ ZIrr ↥M := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hx.2.1.mem_ZIrr
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul n x _ hx => exact Submodule.smul_mem _ n hx
  refine ⟨⟨ζ - ζ.conj, ⟨?_, ?_⟩, ?_⟩, ext', ?_, ?_, ?_⟩
  · -- `ζ − ζ̄ ∈ ℤ[S(HC)]`
    exact Submodule.sub_mem _ (Submodule.subset_span hζmem) (Submodule.subset_span hζcmem)
  · -- `ζ − ζ̄` is `A₀`-supported
    exact hyp.zeta_sub_conj_support hG hodd hζS hζirr
  · -- `ζ − ζ̄ ≠ 0`
    intro h
    exact hζne (sub_eq_zero.mp h).symm
  · -- **isometry on `ℤ[S(HC)]`**
    intro φ ψ hφ hψ
    have hφc := hspan_conj φ hφ
    have hψc := hspan_conj ψ hψ
    rw [hext'apply φ, hext'apply ψ, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
      neg_neg, (hyp.SHC_isCoherent hG).extension_inner_eq _ _ hφc hψc,
      OddOrder.RepresentationTheory.inner_conj_conj]
    obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int (hspan_ZIrr φ hφ) (hspan_ZIrr ψ hψ)
    rw [hm, star_intCast]
  · -- **agrees with `τ` on `ℤ[S(HC), A₀]`** — uses `S(HC) = {ζ, ζ̄}`
    rintro φ ⟨hφspan, hφsupp⟩
    -- `S(HC) = {ζ, ζ̄}` as sets, so `ℤ[S(HC)] = span{ζ, ζ̄}`.
    have hset_eq : SHCset = {ζ, ζ.conj} := by
      apply Set.eq_of_subset_of_subset
      · rintro x ⟨hxS, hxirr, hx1⟩
        exact htwo x hxS hxirr hx1
      · rintro x (rfl | rfl)
        · exact hζmem
        · exact hζcmem
    have hφpair : φ ∈ Submodule.span ℤ ({ζ, ζ.conj} : Set (ClassFunction ↥M ℂ)) := by
      rwa [OddOrder.Peterfalvi.S07.zSpan, hset_eq] at hφspan
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hφpair
    -- support in `A₀` (which excludes `1`) forces the value at `1` to vanish, so `a + b = 0`.
    have h1notA : (1 : ↥M) ∉ hyp.A0 := by
      intro h1
      have hg : ((1 : ↥M) : G) ∈ typePA0 M hyp.typeP := h1
      rw [OneMemClass.coe_one] at hg
      exact hyp.dadeData.dade.ne_one hg rfl
    have hφ1 : φ 1 = 0 := by
      by_contra hne
      exact h1notA (hφsupp (Function.mem_support.mpr hne))
    have hval1 : (a : ℂ) * (hyp.w1 : ℂ) + (b : ℂ) * (hyp.w1 : ℂ) = 0 := by
      have hc := congrArg (fun f : ClassFunction ↥M ℂ => (f : ↥M → ℂ) 1) hab
      simp only [← Int.cast_smul_eq_zsmul ℂ, ClassFunction.add_apply,
        ClassFunction.smul_apply] at hc
      rw [hζ1, hζc1] at hc
      rw [hc]; exact hφ1
    have hw1ne : (hyp.w1 : ℂ) ≠ 0 := by
      have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
      exact_mod_cast (by omega : hyp.w1 ≠ 0)
    have hab0 : a + b = 0 := by
      have hfac : ((a : ℂ) + (b : ℂ)) * (hyp.w1 : ℂ) = 0 := by linear_combination hval1
      have hz : (a : ℂ) + (b : ℂ) = 0 := (mul_eq_zero.mp hfac).resolve_right hw1ne
      exact_mod_cast hz
    have hb : b = -a := by omega
    -- so `φ = a(ζ − ζ̄)`.
    have hφeq : φ = (a : ℤ) • (ζ - ζ.conj) := by
      rw [← hab, hb]; module
    -- both `SHC_swap` and `τ` send `ζ − ζ̄ ↦ ζ^{τ₁} − ζ̄^{τ₁}`.
    have hswapdiff : ext' (ζ - ζ.conj)
        = (hyp.SHC_isCoherent hG).extension ζ - (hyp.SHC_isCoherent hG).extension ζ.conj := by
      rw [map_sub, hext'apply ζ, hext'apply ζ.conj, ClassFunction.conj_conj]
      abel
    have htaudiff : hyp.tau (ζ - ζ.conj)
        = (hyp.SHC_isCoherent hG).extension ζ - (hyp.SHC_isCoherent hG).extension ζ.conj :=
      hyp.tau_zeta_sub_conj_eq_SHC_extension hG (hyp.SHC_isCoherent hG) hodd hζS hζirr hζ1
    rw [hφeq, map_zsmul, map_zsmul, hswapdiff, htaudiff]
  · -- **maps into `ZIrr`**
    intro φ hφ
    rw [hext'apply φ]
    exact neg_mem ((hyp.SHC_isCoherent hG).extension_mem_ZIrr φ.conj (hspan_conj φ hφ))

open scoped FiniteInduce in
/-- **h114 for the branch-2 swap.**  In the second branch of
`tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal` (`S(HC) = {ζ, ζ̄}` and
`(μ₀−ζ)^τ = ∑ω_{r0}^σ + ζ̄^{τ₁}`), the swapped coherent extension `SHC_swap` satisfies the
normalized (11.8.4) identity `(μ₀−ζ)^τ = ∑ω_{r0}^σ − SHC_swap.extension ζ`: indeed
`SHC_swap.extension ζ = −ζ̄^{τ₁}`, so `∑ω − SHC_swap(ζ) = ∑ω + ζ̄^{τ₁} = (μ₀−ζ)^τ`.  This is the
h114-form the (11.8.5) capstone consumes, now available in branch 2 with the swapped `τ₁`. -/
theorem Hypothesis.SHC_swap_h114 [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (htwo : ∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
      lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj)
    (hbranch2 : hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          + (hyp.SHC_isCoherent hG).extension ζ.conj) :
    hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
          - (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension ζ := by
  have := hyp.finiteG
  classical
  have hswapζ : (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension ζ
      = -((hyp.SHC_isCoherent hG).extension ζ.conj) := by
    change (-((hyp.SHC_isCoherent hG).extension.comp
      (ClassFunction.mapRingEquivLinear (G := ↥M) Complex.conjAe.toRingEquiv))) ζ = _
    rw [LinearMap.neg_apply, LinearMap.comp_apply, ClassFunction.mapRingEquivLinear_apply,
      show ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζ = ζ.conj from by
        ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl]
  rw [hswapζ, sub_neg_eq_add, hbranch2]

open scoped FiniteInduce in
/-- **The branch-2 swap commutes with complex conjugation** (the `hconj` P4 input the (11.8.5)
capstone `residualCoeff_eq_zero` needs for the swap branch).  For a degree-`w₁` irreducible
`χ ∈ S(HC)`, `(SHC_swap.extension χ)‾ = SHC_swap.extension χ‾`.  Both sides equal `−SHC(χ‾‾)`:
`SHC_swap.extension φ = −SHC(φ‾)`, so `(SHC_swap χ)‾ = (−SHC(χ‾))‾ = −(SHC(χ‾))‾ = −SHC(χ‾‾)`
(the last by `SHC_extension_conj` at `χ‾`), while `SHC_swap χ‾ = −SHC(χ‾‾)` directly. -/
theorem Hypothesis.SHC_swap_conj [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (htwo : ∀ lam : ClassFunction ↥M ℂ, lam ∈ inducedFamily M → IsIrreducibleCharacter lam →
      lam 1 = (hyp.w1 : ℂ) → lam = ζ ∨ lam = ζ.conj)
    {χ : ClassFunction ↥M ℂ} (hχS : χ ∈ inducedFamily M) (hχirr : IsIrreducibleCharacter χ)
    (hχ1 : χ 1 = (hyp.w1 : ℂ)) :
    ((hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension χ).conj
      = (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension χ.conj := by
  have := hyp.finiteG
  classical
  have hχcS : χ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hχS
  have hχcirr : IsIrreducibleCharacter χ.conj := hχirr.conj
  have hχc1 : χ.conj 1 = (hyp.w1 : ℂ) := by rw [ClassFunction.conj_apply, hχ1, star_natCast]
  have hswap : ∀ φ : ClassFunction ↥M ℂ, (hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo).extension φ
      = -((hyp.SHC_isCoherent hG).extension φ.conj) := fun φ => by
    change (-((hyp.SHC_isCoherent hG).extension.comp
      (ClassFunction.mapRingEquivLinear (G := ↥M) Complex.conjAe.toRingEquiv))) φ = _
    rw [LinearMap.neg_apply, LinearMap.comp_apply, ClassFunction.mapRingEquivLinear_apply,
      show ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ = φ.conj from by
        ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl]
  rw [hswap χ, hswap χ.conj, ClassFunction.conj_neg,
    hyp.SHC_extension_conj hG hχcS hχcirr hχc1]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.4), the h114-producing coherent extension.**  Under the (11.8) contradiction
hypothesis (the residual `(μ₀ − ζ)^τ − ∑_r ω_{r0}^σ` is orthogonal to `(Irr W)^σ`), there is a
coherent extension `ν` of `τ` to `ℤ[S(HC)]` for which the normalized (11.8.4) identity
`(μ₀ − ζ)^τ = ∑_r ω_{r0}^σ − ν.extension ζ` holds.  In the generic (first-branch) case `ν` is the
canonical `SHC_isCoherent`; in the degenerate `S(HC) = {ζ, ζ̄}` case `ν` is the conjugate-swap
`SHC_swap` — Peterfalvi's "we may assume `(μ₀ − ζ)^τ = ∑ω_{i0}^σ − ζ^{τ₁}`" (p. 66), now a clean
`∃`-statement.  This is the interface the (11.8.5) capstone consumes, with its `τ₁`-machinery
taken over an arbitrary coherent extension. -/
theorem Hypothesis.exists_coherent_extension_h114_of_orthogonal [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (horth : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
          - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0) :
    ∃ ν : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0,
      (∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M → IsIrreducibleCharacter χ →
        χ 1 = (hyp.w1 : ℂ) → (ν.extension χ).conj = ν.extension χ.conj) ∧
      hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)
        = (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) - ν.extension ζ := by
  rcases hyp.tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal hG hodd hζS hζirr hζ1 horth with
    h1 | ⟨htwo, h2⟩
  · exact ⟨hyp.SHC_isCoherent hG,
      (fun hχS hχirr hχ1 => hyp.SHC_extension_conj hG hχS hχirr hχ1), h1⟩
  · exact ⟨hyp.SHC_swap hG hodd hζS hζirr hζ1 htwo,
      (fun hχS hχirr hχ1 => hyp.SHC_swap_conj hG hodd hζS hζirr hζ1 htwo hχS hχirr hχ1),
      hyp.SHC_swap_h114 hG hodd hζS hζirr hζ1 htwo h2⟩

open scoped Classical in
/-- **Cross-Parseval for a virtual character.**  For `Δ ∈ ZIrr G` and any `φ`,
`⟨φ, Δ⟩ = ∑_{χ : Irr} ⟨φ, χ⟩ · ⟨Δ, χ⟩`.  From the Fourier reconstruction `Δ = ∑_χ ⟨Δ,χ⟩·χ`
(`sum_inner_irreducibleCharacter_smul`) and `inner_smul_right`; the `star` from conjugate-linearity
vanishes because `⟨Δ,χ⟩` is a real integer (`mem_ZIrr_inner_int`). -/
theorem mem_ZIrr_inner_eq_sum_over_irr [Finite G] [Fintype G] [Fintype (IrreducibleCharacter G)]
    [Invertible (Nat.card G : ℂ)] {φ Δ : ClassFunction G ℂ} (hΔ : Δ ∈ ZIrr G) :
    ClassFunction.inner φ Δ
      = ∑ χ : IrreducibleCharacter G,
          ClassFunction.inner φ (χ : ClassFunction G ℂ)
            * ClassFunction.inner Δ (χ : ClassFunction G ℂ) := by
  conv_lhs => rw [← OddOrder.RepresentationTheory.sum_inner_irreducibleCharacter_smul Δ]
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [OddOrder.RepresentationTheory.inner_smul_right]
  obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int χ hΔ
  rw [hm, star_intCast, mul_comm]

end OddOrder.Peterfalvi.S12


