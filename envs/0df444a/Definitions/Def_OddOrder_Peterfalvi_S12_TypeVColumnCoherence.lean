-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_TypeVColumnCoherence
-- name    : OddOrder_Peterfalvi_S12_TypeVColumnCoherence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:23:21.989203+00:00
-- url     : https://prove2.me/theorems/d7a715be-ba78-4d90-83bc-d3440305e01a
-- title:
--   Peterfalvi (10.10.3)–(10.10.4): type V case (c), column characters and coherence glue
-- statement:
--   Formalizes steps (10.10.3)–(10.10.4) of the proof of Theorem (10.10) for case (c) of Definition (8.7) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §10, pp. 58-63): the $a=0$ coefficient computation and the coherence glue.
--
--   Main declarations: `Hypothesis.muGridAlpha_tau_inner_SHC_zeta_of_eight_le_card` (Peterfalvi (10.10.3), the `a = 0` coefficient computation); `Hypothesis.SHC_tau_muGridAlpha_eq_of_eight_le_card` (Peterfalvi (10.10.3)); `Hypothesis.SHC_tau_muGridAlpha_eq_of_eight_le_SHCcount` (Peterfalvi (10.10.3), count form); `Hypothesis.SHC_tau_muColumn_sub_smul_zeta` (Peterfalvi (10.10.4), the column computation).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_TypeVColumnCoherence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_TypeVColumnCoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
import Definitions.Def_OddOrder_Peterfalvi_S12_Props109To1011

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] {M : Subgroup G}

/-- **The (10.10.3) coefficient vanishing, pure arithmetic**: if `c·a² − 4a − 2 ≤ 0` with
`c ≥ 8` (book: `c = |S₁| = 4(w₁−1) ≥ 8` and `n = 2`, so the norm inequality reads
`|S₁|a² − 2an − 2 ≤ 0`), then the integer coefficient `a` is `0`. -/
theorem alpha_coefficient_eq_zero {c a : ℤ} (hc : 8 ≤ c)
    (h : c * a ^ 2 - 4 * a - 2 ≤ 0) : a = 0 := by
  by_contra ha
  have h1 : 1 ≤ a ∨ a ≤ -1 := by omega
  rcases h1 with h1 | h1
  · nlinarith [sq_nonneg a, sq_nonneg (a - 1)]
  · nlinarith [sq_nonneg a, sq_nonneg (a + 1)]

namespace CharacterParameters

variable {hyp : Hypothesis M}

/-- **The (10.10.2) index pin `n = 2`**: with `d = p = 2w₁ − 1` and `δ = −1`, the (10.3)
relation `n·w₁ = d − δ = 2w₁` forces `n = 2`. -/
theorem n_eq_two (params : CharacterParameters hyp) (hw1 : 0 < hyp.w1)
    (hd : (params.d : ℤ) = 2 * (hyp.w1 : ℤ) - 1) (hδ : params.delta = -1) :
    params.n = 2 := by
  have h := params.n_formula
  rw [hd, hδ] at h
  have hw1' : (0 : ℤ) < (hyp.w1 : ℤ) := by exact_mod_cast hw1
  have h2 : (params.n : ℤ) * (hyp.w1 : ℤ) = 2 * (hyp.w1 : ℤ) := by linarith
  have : (params.n : ℤ) = 2 := mul_right_cancel₀ hw1'.ne' h2
  exact_mod_cast this

/-- **The (10.10.2) sign pin `δ = −1`**: with `d = p = 2w₁ − 1` and `w₁ ≥ 3`, the sign
`δ = +1` is impossible — `n·w₁ = d − 1 = 2w₁ − 2` would give `w₁ ∣ 2`.  (The `δ = ±1`
dichotomy is Peterfalvi (10.3), `muColumnSign_eq_one_or_neg_one`.) -/
theorem delta_eq_neg_one (params : CharacterParameters hyp) (hw1 : 3 ≤ hyp.w1)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hd : (params.d : ℤ) = 2 * (hyp.w1 : ℤ) - 1) :
    params.delta = -1 := by
  rcases hδpm with h1 | h
  · exfalso
    have h := params.n_formula
    rw [hd, h1] at h
    have hdvd : (hyp.w1 : ℤ) ∣ 2 := by
      have h2 : ((params.n : ℤ) - 2) * (hyp.w1 : ℤ) = -2 := by linear_combination h
      have : (hyp.w1 : ℤ) ∣ -2 := Dvd.intro_left _ h2
      exact (dvd_neg.mp this)
    have hle : (hyp.w1 : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
    have : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw1
    omega
  · exact h

end CharacterParameters

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.3), the `a = 0` coefficient computation** — the type-V case-(c)
counterpart of the (11.8.2) `muGridAlpha_tau_residual_norm`: projecting `α_{ij}^τ` onto the
orthonormal `S₁^{τ₁} = R` gives a constant coefficient `a` off `ζ^{τ₁}`
(`muGridAlpha_tau_inner_SHC_extension_sub`) and `a − n` at `ζ^{τ₁}`; Parseval + the norm
`‖α_{ij}^τ‖² = 2 + n²` give `(a−n)² + (|R|−1)a² ≤ 2 + n²`, i.e. `|R|·a² − 2an − 2 ≤ 0`.
In the (10.10.3) regime `n = 2` and `|R| = |S₁| = 4(w₁−1) ≥ 8` — as opposed to the
(11.8.1) regime `|R| = n` — this forces `a = 0` (`alpha_coefficient_eq_zero`), so
`⟨α_{ij}^τ, ζ^{τ₁}⟩ = −n`: exactly the `hα0` input of `SHC_tau_muGridAlpha_eq`, whence
`α_{ij}^τ = δ(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}` ((10.10.3)). -/
theorem Hypothesis.muGridAlpha_tau_inner_SHC_zeta_of_eight_le_card [Finite G]
    {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hneq : n = 2)
    {R : Finset (ClassFunction G ℂ)} (hR8 : 8 ≤ R.card)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) :
    ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      (coh.extension ζ) = -(n : ℂ) := by
  classical
  have hζR : coh.extension ζ ∈ R := hRmem ζ hζS hζirr hζ1
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  obtain ⟨c, Y, hcoeff, hnorm, hYorth, hdecomp, hYZ⟩ :=
    inner_self_eq_sum_sq_add_of_intProjection hαZ hZ horth
  set a : ℤ := c (coh.extension ζ) + (n : ℤ) with hadef
  have hcζ : c (coh.extension ζ) = a - (n : ℤ) := by rw [hadef]; ring
  have hcη : ∀ β ∈ R, β ≠ coh.extension ζ → c β = a := by
    intro β hβR hβne
    obtain ⟨η, hηS, hηirr, hη1, rfl⟩ := hRrev β hβR
    have hηζ : η ≠ ζ := fun h => hβne (by rw [h])
    have hsub := hyp.muGridAlpha_tau_inner_SHC_extension_sub hG coh hodd i hj0 hζS hζirr hζ1
      hηS hηirr hη1 hηζ hdeg hμ0 hnf hδj hdζ h0ζ
    rw [hcoeff _ hζR, hcoeff _ (hRmem η hηS hηirr hη1)] at hsub
    have hcast : ((c (coh.extension η) : ℤ) : ℂ) = ((a : ℤ) : ℂ) := by
      rw [hadef]; push_cast; linear_combination -hsub
    exact_mod_cast hcast
  have hsplit := sum_sq_eq_of_split hζR hcζ hcη
  have hnorm2 := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  rw [hnorm2, hsplit] at hnorm
  have hineq : (a - (n : ℤ)) ^ 2 + ((R.card : ℤ) - 1) * a ^ 2 ≤ 2 + (n : ℤ) ^ 2 := by
    apply int_le_of_add_inner_self_eq (Y := Y)
    push_cast at hnorm ⊢
    linear_combination -hnorm
  have hc8 : (8 : ℤ) ≤ (R.card : ℤ) := by exact_mod_cast hR8
  have ha0 : a = 0 := by
    refine alpha_coefficient_eq_zero hc8 ?_
    subst hneq
    push_cast at hineq
    nlinarith [hineq]
  have hval := hcoeff _ hζR
  rw [hcζ, ha0] at hval
  rw [hval]
  push_cast
  ring

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.3)** (grid form): in the (10.10.3) regime — `n = 2` and an orthonormal
`S₁^{τ₁} = R` with `|R| ≥ 8` — the Dade image of the (10.5) difference is
`α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}` with `ζ^{τ₁}` the `S₁`-coherent extension.
Composition of the `a = 0` coefficient computation
(`muGridAlpha_tau_inner_SHC_zeta_of_eight_le_card`) with the SHC (10.5) endgame
(`SHC_tau_muGridAlpha_eq`). -/
theorem Hypothesis.SHC_tau_muGridAlpha_eq_of_eight_le_card [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hneq : n = 2)
    {R : Finset (ClassFunction G ℂ)} (hR8 : 8 ≤ R.card)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - (n : ℂ) • coh.extension ζ :=
  hyp.SHC_tau_muGridAlpha_eq hG coh hodd i hj0 hζS hζirr hζ1 hζne hdeg hμ0 hnf hδj hdζ h0ζ hδpm
    (hyp.muGridAlpha_tau_inner_SHC_zeta_of_eight_le_card hG coh hodd i hj0 hζS hζirr hζ1
      hdeg hμ0 hnf hδj hdζ h0ζ hδpm hneq hR8 hZ horth hRmem hRrev)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.3), count form** (R-free): with `n = 2` and at least `8` degree-`w₁`
irreducible members of `S` — the (10.10.2) count is `|S₁| = 4(w₁−1) ≥ 8` for `w₁ ≥ 3` —
the (10.5) difference maps to `α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`.  The
orthonormal family `S₁^{τ₁}` and its cardinality are supplied by
`exists_SHC_extension_orthonormal`. -/
theorem Hypothesis.SHC_tau_muGridAlpha_eq_of_eight_le_SHCcount [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hneq : n = 2)
    (h8 : 8 ≤ (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - (n : ℂ) • coh.extension ζ := by
  obtain ⟨R, hZ, horth, hRmem, hRrev, hcard⟩ := hyp.exists_SHC_extension_orthonormal hG coh
  exact hyp.SHC_tau_muGridAlpha_eq_of_eight_le_card hG coh hodd i hj0 hζS hζirr hζ1 hζne
    hdeg hμ0 hnf hδj hdζ h0ζ hδpm hneq (by rw [hcard]; exact h8) hZ horth hRmem hRrev

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.4), the column computation**: summing the (10.10.3) images
`α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}` over the `w₁` rows and pinning the first
column by (10.9) gives the coherent-extension glue for the column character
`μ_j = ∑_i μ_{ij}`:

`(μ_j − d·ζ)^τ = δ·(μ_0 − ζ)^τ + ∑_i α_{ij}^τ = δ·∑_i ω_{ij}^σ − d·ζ^{τ₁}`.

The `ζ`-coefficient collapses through `n·w₁ = d − δ` (`hnf`): on the source side
`−δ − n·w₁ = −d` (so `μ_j − d·ζ = δ·(μ_0 − ζ) + ∑_i α_{ij}` is exact), and on the image side
`δ + n·w₁ = d` reassembles the `−d·ζ^{τ₁}` tail.  The (10.9) pin
`(μ_0 − ζ)^τ = ∑_i ω_{i0}^σ − ζ^{τ₁}` is supplied separately as `hpin`. -/
theorem Hypothesis.SHC_tau_muColumn_sub_smul_zeta [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : ∀ i, hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : ∀ i, hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : ∀ i, hyp.muGrid hG hodd i j 1 ≠ ζ 1)
    (h0ζ : ∀ i, hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hneq : n = 2)
    (h8 : 8 ≤ (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card)
    (hpin : hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0) - coh.extension ζ) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
      = (δ : ℂ) • (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        - (d : ℂ) • coh.extension ζ := by
  -- the (10.3) index relation, cast to `ℂ`: `d = δ + w₁·n`
  have hd' : (d : ℂ) = (δ : ℂ) + (hyp.w1 : ℂ) * (n : ℂ) := by
    have h := congrArg (Int.cast : ℤ → ℂ) hnf
    push_cast at h
    linear_combination -h
  -- the per-row (10.10.3) images `α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`
  have htau_i : ∀ i : Fin hyp.w1, hyp.tau (hyp.muGrid hG hodd i j
        - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0) - (n : ℂ) • coh.extension ζ := fun i =>
    hyp.SHC_tau_muGridAlpha_eq_of_eight_le_SHCcount hG coh hodd i hj0 hζS hζirr hζ1 hζne
      (hdeg i) (hμ0 i) hnf hδj (hdζ i) (h0ζ i) hδpm hneq h8
  -- the `δ`-scaled (10.9) pin `(δ·(μ_0 − ζ))^τ = δ·(∑_i ω_{i0}^σ − ζ^{τ₁})`
  have hpinδ : hyp.tau ((δ : ℂ) • ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ))
      = (δ : ℂ) • ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
          - coh.extension ζ) := by
    rw [Int.cast_smul_eq_zsmul ℂ δ ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ),
      map_zsmul, hpin, Int.cast_smul_eq_zsmul ℂ δ]
  -- source-side regrouping `μ_j − d·ζ = δ·(μ_0 − ζ) + ∑_i α_{ij}` (ζ-coefficient `−δ − n·w₁ = −d`)
  have hsum_mu : ∑ i : Fin hyp.w1, (hyp.muGrid hG hodd i j
        - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
        - (δ : ℂ) • (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0)
        - ((hyp.w1 : ℂ) * (n : ℂ)) • ζ := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hsrc : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ
      = (δ : ℂ) • ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
        + ∑ i : Fin hyp.w1, (hyp.muGrid hG hodd i j
            - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) := by
    rw [hsum_mu, hd']
    module
  -- image-side collapse of the `α`-sum
  have hsum_om : ∑ i : Fin hyp.w1, ((δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
        - hyp.alignedOmegaSigmaGrid hG hodd i 0) - (n : ℂ) • coh.extension ζ)
      = (δ : ℂ) • ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
          - (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0))
        - ((hyp.w1 : ℂ) * (n : ℂ)) • coh.extension ζ := by
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum (r := (δ : ℂ)), Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul]
  rw [hsrc, map_add, map_sum, hpinδ]
  simp only [htau_i]
  rw [hsum_om, hd']
  module

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.9)/(10.10.4), the column-`0` pin**: `(μ_0 − ζ)^τ = ∑_i ω_{i0}^σ − ζ^{τ₁}`,
where `ζ^{τ₁} = coh.extension ζ` is the `S₁ = S(HC)`-coherent extension — the residual `χ` of the
(10.9) decomposition **identified** with `ζ^{τ₁}` (book: "As `(α_{ij}, μ_0 − ζ) = −δ + n`, it
follows from (10.9), (10.10.1) and (10.10.3) that `(μ_0 − ζ)^τ = ∑_{0≤i<w₁} ω_{i0}^σ − ζ^{τ₁}`").

The coherence-free (10.9) σ-coefficient form
(`inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2`, hence the hypothesis `w₁ < w₂`)
pins `⟨ψ, ω_{ij}^σ⟩ = [j = 0]` for `ψ = (μ_0 − ζ)^τ`, and the Dade isometry gives
`‖ψ‖² = ‖μ_0 − ζ‖² = w₁ + 1` (`inner_muColumnZero_sub_zeta_self`), so the residual
`χ = ∑_i ω_{i0}^σ − ψ` has `‖χ‖² = w₁ − w₁ − w₁ + (w₁ + 1) = 1`.  The identification is the
(10.10.4) pairing: transporting `(α_{0j}, μ_0 − ζ) = n − δ` through the Dade isometry
(`muGridAlpha_tau_inner_zeroColumnSum_sub_zeta`) and expanding `α_{0j}^τ` by (10.10.3)
(`SHC_tau_muGridAlpha_eq_of_eight_le_SHCcount`) forces `⟨ζ^{τ₁}, ψ⟩ = −1` (using `n = 2 ≠ 0`);
with `⟨ζ^{τ₁}, ∑_i ω_{i0}^σ⟩ = 0` (`SHC_extension_inner_zeroColumnOmegaSigma_sum`, (5.3.b)) this
gives `⟨ζ^{τ₁}, χ⟩ = 1`, and `‖ζ^{τ₁}‖² = 1 = ‖χ‖²` collapses
`‖ζ^{τ₁} − χ‖² = 1 − 1 − 1 + 1 = 0`, i.e. `χ = ζ^{τ₁}` (positive-definiteness).  This discharges
the `hpin` input of `SHC_tau_muColumn_sub_smul_zeta`. -/
theorem Hypothesis.SHC_tau_muColumnZero_sub_zeta [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : ∀ i, hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : ∀ i, hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : ∀ i, hyp.muGrid hG hodd i j 1 ≠ ζ 1)
    (h0ζ : ∀ i, hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hneq : n = 2)
    (h8 : 8 ≤ (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card)
    (hw12 : hyp.w1 < hyp.w2) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0) - coh.extension ζ := by
  classical
  -- `w₁ ≥ 3`, so the row `0` for the (10.10.4) α-pairing exists
  have h3 : (3 : ℕ) ≤ hyp.w1 :=
    (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  have : NeZero hyp.w1 := ⟨by omega⟩
  -- the (10.9) coherence-free σ-coefficients: `⟨ψ, ω_{ij'}^σ⟩ = [j' = 0]`
  have hψω : ∀ (i : Fin hyp.w1) (j' : Fin hyp.w2),
      ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hodd i j') = (if j' = 0 then (1 : ℂ) else 0) :=
    fun i j' =>
      inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2 hG hyp hζS hζirr hζ1 hw12 i j'
  have hωψ : ∀ (i : Fin hyp.w1) (j' : Fin hyp.w2),
      ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hodd i j')
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        = (if j' = 0 then (1 : ℂ) else 0) := by
    intro i j'
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hψω i j']
    by_cases hj' : j' = 0 <;> simp [hj']
  -- the (10.10.4) pairing: `⟨ζ^{τ₁}, ψ⟩ = −1`
  have hzψ : ClassFunction.inner (coh.extension ζ)
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = -1 := by
    have hpair := hyp.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta hG hodd 0 hj0 hζS hζirr hζ1
      (hdeg 0) (hμ0 0) hnf hδj (hdζ 0) (h0ζ 0)
    rw [hyp.SHC_tau_muGridAlpha_eq_of_eight_le_SHCcount hG coh hodd 0 hj0 hζS hζirr hζ1 hζne
      (hdeg 0) (hμ0 0) hnf hδj (hdζ 0) (h0ζ 0) hδpm hneq h8] at hpair
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left] at hpair
    rw [hωψ 0 j, hωψ 0 0, if_neg hj0, if_pos rfl] at hpair
    have hn : ((n : ℕ) : ℂ) = 2 := by rw [hneq]; norm_num
    rw [hn] at hpair
    linear_combination (-1 / 2 : ℂ) * hpair
  -- (5.3.b): `⟨ζ^{τ₁}, ∑_i ω_{i0}^σ⟩ = 0`, and `‖ζ^{τ₁}‖² = 1`
  have hzΩ : ClassFunction.inner (coh.extension ζ)
      (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0) = 0 :=
    hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG coh hodd hζS hζirr hζ1 hζne
  have hzz : ClassFunction.inner (coh.extension ζ) (coh.extension ζ) = 1 :=
    hyp.SHC_extension_inner_self hG coh hζS hζirr hζ1
  -- the (10.9) norm data: `⟨ψ, Ω⟩ = ⟨Ω, ψ⟩ = ⟨Ω, Ω⟩ = w₁` and `⟨ψ, ψ⟩ = w₁ + 1`
  have hsum1 : ∑ _i : Fin hyp.w1, (1 : ℂ) = (hyp.w1 : ℂ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hψΩ : ClassFunction.inner
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
      (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0) = (hyp.w1 : ℂ) := by
    have h1 : ∀ i : Fin hyp.w1, ClassFunction.inner
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hodd i 0) = 1 := fun i => by
      rw [hψω i 0, if_pos rfl]
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl (fun i _ => h1 i), hsum1]
  have hΩψ : ClassFunction.inner (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = (hyp.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hψΩ, star_natCast]
  have hΩΩ : ClassFunction.inner (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
      (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0) = (hyp.w1 : ℂ) := by
    have h1 : ∀ i : Fin hyp.w1, ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hodd i 0)
        (∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i' 0) = 1 := by
      intro i
      rw [OddOrder.RepresentationTheory.inner_sum_right, Finset.sum_eq_single i]
      · rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i i 0 0, if_pos ⟨rfl, rfl⟩]
      · intro i' _ hi'
        rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i i' 0 0,
          if_neg (fun hh => hi' hh.1.symm)]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [inner_sum_left, Finset.sum_congr rfl (fun i _ => h1 i), hsum1]
  have hψψ : ClassFunction.inner
      (hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ))
      (hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)) = ((hyp.w1 + 1 : ℕ) : ℂ) := by
    have hsupp : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ).support ⊆ hyp.A0 :=
      hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
    rw [hyp.tau_inner_eq_of_supported hsupp hsupp]
    exact inner_muColumnZero_sub_zeta_self hG hyp hζirr hζ1
  -- transposed values (conjugate symmetry; all values are real)
  have hψz : ClassFunction.inner
      (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) (coh.extension ζ) = -1 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hzψ]
    simp
  have hΩz : ClassFunction.inner (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
      (coh.extension ζ) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hzΩ, star_zero]
  -- Cauchy–Schwarz equality: `‖ζ^{τ₁} − (Ω − ψ)‖² = 1 − 1 − 1 + 1 = 0`, so `ζ^{τ₁} = Ω − ψ`
  have hzero : ClassFunction.inner
      (coh.extension ζ - ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)))
      (coh.extension ζ - ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ))) = 0 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, hzz, hzΩ, hzψ,
      hΩz, hΩΩ, hΩψ, hψz, hψΩ, hψψ]
    push_cast
    ring
  have heq : coh.extension ζ
      = (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) :=
    sub_eq_zero.mp (eq_zero_of_inner_self_re_eq_zero
      (φ := coh.extension ζ - ((∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ)))
      (by rw [hzero]; exact Complex.zero_re))
  rw [heq, sub_sub_cancel]

open scoped FiniteInduce in
/-- **§10 column Gram matrix** (Peterfalvi (4.3.b)/(10.10.4)): the column characters
`μ_j = ∑_i μ_{ij}` of the (10.3) grid are pairwise orthogonal of squared norm `w₁`,
`⟨μ_j, μ_k⟩ = w₁·[j = k]`.  The grid `μ_{ij}` is orthonormal (`muGrid_inner_self`,
`muGrid_inner_within_column`, `muGrid_inner_cross_column`), so the double sum collapses to
the `w₁` diagonal terms.  This is the source half of the (10.10.4) isometry check
`‖μ_j‖² = w₁ = ‖δ·∑_i ω_{ij}^σ‖²` for the glued extension `ν`. -/
theorem Hypothesis.muColumnSum_inner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (j k : Fin hyp.w2) :
    ClassFunction.inner (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
        (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      = if j = k then (hyp.w1 : ℂ) else 0 := by
  classical
  rw [inner_sum_left]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl]
    have hrow : ∀ i : Fin hyp.w1, ClassFunction.inner (hyp.muGrid hG hodd i j)
        (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j) = 1 := by
      intro i
      rw [OddOrder.RepresentationTheory.inner_sum_right, Finset.sum_eq_single i]
      · exact hyp.muGrid_inner_self hG hodd i j
      · intro i' _ hi'
        exact hyp.muGrid_inner_within_column hG hodd j (Ne.symm hi')
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · rw [if_neg hjk]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_eq_zero fun i' _ => hyp.muGrid_inner_cross_column hG hodd i i' hjk

open scoped FiniteInduce in
/-- **§10 σ-column Gram matrix** ((3.2) isometry on the aligned grid, summed): the column sums
`Ω_j = ∑_i ω_{ij}^σ` of the orthonormal σ-grid (`alignedOmegaSigmaGrid_inner`) are pairwise
orthogonal of squared norm `w₁`, `⟨Ω_j, Ω_k⟩ = w₁·[j = k]`.  This is the image half of the
(10.10.4) isometry check for the glued extension `ν(μ_j) = δ·Ω_j`. -/
theorem Hypothesis.omegaSigmaColumnSum_inner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (j k : Fin hyp.w2) :
    ClassFunction.inner (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i k)
      = if j = k then (hyp.w1 : ℂ) else 0 := by
  classical
  rw [inner_sum_left]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl]
    have hrow : ∀ i : Fin hyp.w1,
        ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hodd i j)
          (∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i' j) = 1 := by
      intro i
      rw [OddOrder.RepresentationTheory.inner_sum_right, Finset.sum_eq_single i]
      · rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i i j j, if_pos ⟨rfl, rfl⟩]
      · intro i' _ hi'
        rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i i' j j,
          if_neg (fun hh => hi' hh.1.symm)]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · rw [if_neg hjk]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i i' j k, if_neg (fun hh => hjk hh.2)]

open scoped FiniteInduce in
/-- **§10 column ⊥ degree-distinct irreducible** (Peterfalvi (10.5)/(10.10.4)): the column
character `μ_j = ∑_i μ_{ij}` is orthogonal to any irreducible `χ` whose degree differs from
every grid entry of the column, `⟨μ_j, χ⟩ = ∑_i ⟨μ_{ij}, χ⟩ = 0`
(`muGrid_inner_eq_zero_of_apply_one_ne` per row).  With `χ = η ∈ S₁` (degree `w₁ ≠ d`) this is
the source-orthogonality `{μ_j} ⊥ S₁` of the (10.10.4) union glue. -/
theorem Hypothesis.muColumnSum_inner_eq_zero_of_apply_one_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (j : Fin hyp.w2) {χ : ClassFunction ↥M ℂ}
    (hχirr : IsIrreducibleCharacter χ)
    (hne : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i j 1 ≠ χ 1) :
    ClassFunction.inner (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) χ = 0 := by
  rw [inner_sum_left]
  exact Finset.sum_eq_zero fun i _ =>
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hχirr (hne i)

open OddOrder.GroupTheory in
open scoped FiniteInduce in
/-- **Peterfalvi (10.10.4), `μ_j − d·ζ ∈ ℤ[S, A₀]` (support half)**: the column character
`μ_j = ∑_i μ_{ij}` (degree `d·w₁` by `hdeg`) minus `d·ζ` (`ζ ∈ S` of degree `w₁`) is supported
in `A_0(M)`.  Both vanish off `M' = [M,M]` (`muGrid_column_sum_vanishes_off_derived`; `ζ` is
induced from the normal `M'`), and the degrees cancel at `1`, so the support lies in
`M'^# ∩ C_M ≠ ∅ ⊆ A(M) ⊆ A_0(M)`.  The `d = 1`, `j = 0` case is
`muColumnZero_sub_zeta_support`; this is the general-column version feeding the (10.10.4)
diagonal set `D = {μ_j − d·ζ}` and its `A₀`-supported generation argument. -/
theorem Hypothesis.muColumnSum_sub_smul_zeta_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {j : Fin hyp.w2}
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    {d : ℕ} (hdeg : ∀ i, hyp.muGrid hG hodd i j 1 = (d : ℂ)) :
    ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ).support ⊆ hyp.A0 := by
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else both `μ_j` and `ζ` vanish at `z`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, hyp.muGrid_column_sum_vanishes_off_derived hG hodd j hzK,
      ClassFunction.smul_apply, hζvanish hzK, mul_zero, sub_zero]
  -- `z ≠ 1`: `(μ_j − d·ζ)(1) = w₁·d − d·w₁ = 0`.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, ClassFunction.smul_apply, hζ1,
      ClassFunction.finset_sum_apply, Finset.sum_congr rfl (fun i _ => hdeg i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  have hmem : (z : G) ∈ typePA0 M hyp.typeP := by
    unfold typePA0
    rw [Set.mem_union]
    left
    exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
      ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  exact hmem

open scoped Classical FiniteInduce in
/-- **The (10.10.4) column image map**: an integral character map sending each nonzero-column
character `μ_j = ∑_i μ_{ij}` to its (10.10.3) coherent target `δ·∑_i ω_{ij}^σ`.  Fourier
reconstruction over the pairwise-orthogonal columns (`coherentImageMap` with the `⟨μ_j, μ_j⟩ = w₁`
rescaling of `coherentImageMap_apply_eq_of_orthogonal`); the values off `ℤ[{μ_j}]` are
immaterial — only these column values feed the (10.10.4) glue
`exists_integralCharacterMap_glue_of_orthogonal`. -/
theorem Hypothesis.exists_muColumnSum_imageMap [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (δ : ℤ) (hw1 : 0 < hyp.w1) :
    ∃ νX : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G,
      ∀ (j : Fin hyp.w2), j ≠ 0 →
        νX (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
          = (δ : ℂ) • ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j := by
  classical
  have hw1C : (hyp.w1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hw1.ne'
  let e : Fin (Fintype.card {j : Fin hyp.w2 // j ≠ 0}) ≃ {j : Fin hyp.w2 // j ≠ 0} :=
    (Fintype.equivFin {j : Fin hyp.w2 // j ≠ 0}).symm
  let χ : Fin (Fintype.card {j : Fin hyp.w2 // j ≠ 0}) → ClassFunction ↥M ℂ :=
    fun a => ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (e a).1
  let T : Fin (Fintype.card {j : Fin hyp.w2 // j ≠ 0}) → ClassFunction G ℂ :=
    fun a => (δ : ℂ) • ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i (e a).1
  have horth : ∀ a b, a ≠ b → ClassFunction.inner (χ a) (χ b) = 0 := by
    intro a b hab
    simp only [χ]
    rw [hyp.muColumnSum_inner hG hodd (e a).1 (e b).1,
      if_neg (fun hv => hab (e.injective (Subtype.ext hv)))]
  have hnorm : ∀ a, ClassFunction.inner (χ a) (χ a) ≠ 0 := by
    intro a
    simp only [χ]
    rw [hyp.muColumnSum_inner hG hodd (e a).1 (e a).1, if_pos rfl]
    exact hw1C
  refine ⟨OddOrder.Peterfalvi.S07.IntegralCharacterMap.coherentImageMap χ
    (fun a => (ClassFunction.inner (χ a) (χ a))⁻¹ • T a), fun j hj => ?_⟩
  have h := OddOrder.Peterfalvi.S07.IntegralCharacterMap.coherentImageMap_apply_eq_of_orthogonal
    (χ := χ) (X := T) horth hnorm (e.symm ⟨j, hj⟩)
  simpa only [χ, T, Equiv.apply_symm_apply] using h

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.4) — the type-V case-(c) coherence engine**: `S` is coherent.

Book: "Set `ν(μ_j) = δ·∑_{0≤i<w₁} ω_{ij}^σ` for `0 < j < w₂` and `ν = τ₁` on `ℤ[S₁]`.  As
`(μ_j − d·ζ)^τ = δ·∑_i ω_{ij}^σ − d·ζ^{τ₁}`, `ν` is a coherent extension of `τ` to `ℤ[S]`."
The glued map `ν := (τ₁ on ℤ[S₁]) ⊕ (μ_j ↦ δ·Ω_j^σ)` is assembled by the S07 Fourier glue
(`exists_integralCharacterMap_glue_of_orthogonal` + `exists_muColumnSum_imageMap`) and fed to
the diagonal-aware union engine
`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` with `X = {μ_j | j ≠ 0}`,
`Y = S₁ = S(HC)` (coherent by `coh` = (5.7)), and diagonal set `D = {μ_j − d·ζ | j ≠ 0}`:

* `hDτ` — `ν(μ_j − d·ζ) = (μ_j − d·ζ)^τ` is the landed (10.10.4) image computation
  (`SHC_tau_muColumn_sub_smul_zeta` ∘ `SHC_tau_muColumnZero_sub_zeta`);
* `cX` — the `{μ_j}`-coherence: isometry from the two column Gram matrices
  (`muColumnSum_inner` / `omegaSigmaColumnSum_inner`, `δ² = 1`), `τ`-agreement on
  `ℤ[{μ_j}, A₀]` through `ℤ[D]` (a supported column combination has coefficient sum `0` since
  `1 ∉ A₀` and all degrees are `d·w₁ ≠ 0`), targets in `ℤ[Irr G]`
  (`alignedOmegaSigmaGrid_mem_ZIrr`);
* `hgen` — generation: an `A₀`-supported element of `ℤ[X ∪ S₁]` splits as
  `∑ c_j·(μ_j − d·ζ) ∈ ℤ[D]` plus an `A₀`-supported member of `ℤ[S₁]` (each `μ_j − d·ζ` is
  `A₀`-supported, `muColumnSum_sub_smul_zeta_support`);
* `hmixed`/`hsrc_ortho` — `{μ_j} ⊥ S₁` on both sides: source by degree
  (`muColumnSum_inner_eq_zero_of_apply_one_ne`), image by (5.3.b)
  (`SHC_extension_inner_alignedOmegaSigma_eq_zero`).

The **(10.10.2) structure** `S − S₁ = {μ_j | j ≠ 0}` is taken as the engine hypothesis
`hstruct` (the reverse inclusion `μ_j ∈ S` is genuine, `muGrid_column_sum_mem_inducedFamily`);
its discharge — the `p³`-group character theory of case (c) — is the separate (10.10.2) leg
(issue 1021).  The numeric pins `n = 2`, `δ = ±1`, `|S₁| ≥ 8`, `w₁ < w₂` enter as hypotheses
exactly as in the landed (10.10.3)/(10.9) computations. -/
noncomputable def Hypothesis.typeV_caseC_coherence_engine [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : ∀ i, hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hodd j = δ)
    (hdζ : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → hyp.muGrid hG hodd i j 1 ≠ ζ 1)
    (h0ζ : ∀ i, hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hneq : n = 2)
    (h8 : 8 ≤ (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card)
    (hw12 : hyp.w1 < hyp.w2)
    (hstruct : ∀ φ ∈ hyp.Sset, φ ∈ hyp.SHCSet ∨
      ∃ j : Fin hyp.w2, j ≠ 0 ∧ φ = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0 := by
  classical
  -- `ζ ∈ S₁ = S(HC)`
  have hζSHC : ζ ∈ hyp.SHCSet := ⟨hζS, hζirr, hζ1⟩
  -- numerology: `w₁ ≥ 3` and `d = 2w₁ + δ ≥ 5`
  have h3 : (3 : ℕ) ≤ hyp.w1 :=
    (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  have hw1C : (hyp.w1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd5 : 5 ≤ d := by
    have h3' : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast h3
    have hnf' := hnf
    rw [hneq] at hnf'
    push_cast at hnf'
    have : (5 : ℤ) ≤ (d : ℤ) := by rcases hδpm with rfl | rfl <;> omega
    exact_mod_cast this
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- `1 ∉ A₀` (the Dade support is a subset of `M^#`)
  have h1A0 : (1 : ↥M) ∉ hyp.A0 := fun h =>
    hyp.dadeData.dade.ne_one h (by simp)
  -- supported class functions vanish off `A₀`
  have hsupp_val : ∀ (ψ : ClassFunction ↥M ℂ), ψ.support ⊆ hyp.A0 →
      ∀ z, z ∉ hyp.A0 → ψ z = 0 := fun ψ hψ z hz => by
    by_contra h0
    exact hz (hψ (ClassFunction.mem_support.mpr h0))
  -- the column set `X = {μ_j | j ≠ 0}` and the diagonal set `D = {μ_j − d·ζ | j ≠ 0}`
  set Xc : Set (ClassFunction ↥M ℂ) :=
    {φ | ∃ j : Fin hyp.w2, j ≠ 0 ∧ φ = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j} with hXc_def
  set Dset : Set (ClassFunction ↥M ℂ) :=
    {φ | ∃ j : Fin hyp.w2, j ≠ 0 ∧
      φ = (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ} with hDset_def
  have hXc_range : Xc = Set.range (fun jj : {j : Fin hyp.w2 // j ≠ 0} =>
      ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i jj.1) := by
    ext φ
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨jj, rfl⟩; exact ⟨jj.1, jj.2, rfl⟩
  -- degrees: `μ_j(1) = w₁·d`
  have hμ1 : ∀ (j : Fin hyp.w2), j ≠ 0 →
      (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) 1 = (hyp.w1 : ℂ) * (d : ℂ) := by
    intro j hj
    rw [ClassFunction.finset_sum_apply, Finset.sum_congr rfl (fun i _ => hdeg i j hj),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- source orthogonality `{μ_j} ⊥ S₁` (pairwise)
  have hXY : ∀ x ∈ Xc, ∀ y ∈ hyp.SHCSet, ClassFunction.inner x y = 0 := by
    rintro x ⟨j, hj, rfl⟩ y hy
    refine hyp.muColumnSum_inner_eq_zero_of_apply_one_ne hG hodd j hy.2.1 ?_
    intro i
    rw [hy.2.2, ← hζ1]
    exact hdζ i j hj
  -- no real characters in `S` (odd order)
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  -- the glued integral map `ν`: `ν(μ_j) = δ·Ω_j^σ`, `ν = τ₁` on `S₁`
  have hνXex := hyp.exists_muColumnSum_imageMap hG hodd δ (by omega)
  have hXfin : Xc.Finite := by rw [hXc_range]; exact Set.finite_range _
  have hYfin : hyp.SHCSet.Finite := inducedFamily_finite.subset (fun φ hφ => hφ.1)
  have hXorth : ∀ x ∈ Xc, ∀ x' ∈ Xc, x ≠ x' → ClassFunction.inner x x' = 0 := by
    rintro x ⟨j, hj, rfl⟩ x' ⟨k, hk, rfl⟩ hne
    rw [hyp.muColumnSum_inner hG hodd j k, if_neg (fun hv => hne (by rw [hv]))]
  have hXnorm : ∀ x ∈ Xc, ClassFunction.inner x x ≠ 0 := by
    rintro x ⟨j, hj, rfl⟩
    rw [hyp.muColumnSum_inner hG hodd j j, if_pos rfl]
    exact hw1C
  have hYorth : ∀ y ∈ hyp.SHCSet, ∀ y' ∈ hyp.SHCSet, y ≠ y' →
      ClassFunction.inner y y' = 0 := fun y hy y' hy' hne =>
    inducedFamily_pairwiseOrthogonal hy.1 hy'.1 hne
  have hYnorm : ∀ y ∈ hyp.SHCSet, ClassFunction.inner y y ≠ 0 := fun y hy => by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hy.2.1 hy.2.1, if_pos rfl]
    exact one_ne_zero
  have hglue :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthogonal
      hXfin hYfin hXorth hXnorm hYorth hYnorm hXY hνXex.choose coh.extension
  set ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G := hglue.choose with hν_def
  have hνX : ∀ x ∈ Xc, ν x = hνXex.choose x := hglue.choose_spec.1
  have hνY : ∀ y ∈ hyp.SHCSet, ν y = coh.extension y := hglue.choose_spec.2
  have hνcol : ∀ (j : Fin hyp.w2), j ≠ 0 →
      ν (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
        = (δ : ℂ) • ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j := fun j hj =>
    (hνX _ ⟨j, hj, rfl⟩).trans (hνXex.choose_spec j hj)
  -- the landed (10.10.4) image computation: `(μ_j − d·ζ)^τ = δ·Ω_j^σ − d·ζ^{τ₁}`
  have hτD : ∀ (j : Fin hyp.w2), j ≠ 0 →
      hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ)
        = (δ : ℂ) • (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
          - (d : ℂ) • coh.extension ζ := fun j hj =>
    hyp.SHC_tau_muColumn_sub_smul_zeta hG coh hodd hj hζS hζirr hζ1 hζne
      (fun i => hdeg i j hj) hμ0 hnf (hδj j hj) (fun i => hdζ i j hj) h0ζ hδpm hneq h8
      (hyp.SHC_tau_muColumnZero_sub_zeta hG coh hodd hj hζS hζirr hζ1 hζne
        (fun i => hdeg i j hj) hμ0 hnf (hδj j hj) (fun i => hdζ i j hj) h0ζ hδpm hneq h8 hw12)
  -- `ν` matches `τ` on the diagonal set `D`
  have hDτ : ∀ dg ∈ Dset, ν dg = hyp.tau dg := by
    rintro dg ⟨j, hj, rfl⟩
    rw [hτD j hj, map_sub, hνcol j hj]
    congr 1
    rw [Nat.cast_smul_eq_nsmul ℂ d ζ, map_nsmul, hνY ζ hζSHC,
      Nat.cast_smul_eq_nsmul ℂ d (coh.extension ζ)]
  -- supports of the diagonal generators
  have hDsupp : ∀ (j : Fin hyp.w2), j ≠ 0 →
      ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) - (d : ℂ) • ζ).support ⊆ hyp.A0 :=
    fun j hj => hyp.muColumnSum_sub_smul_zeta_support hG hodd hζS hζ1 (fun i => hdeg i j hj)
  -- ### the `{μ_j}`-side coherence `cX` (extension := ν)
  -- (nonzero) `μ_1 − μ_2` is a nonzero `A₀`-supported member of `ℤ[X]`
  have hw24 : 4 ≤ hyp.w2 := by omega
  have hnonzero : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) Xc hyp.A0 ∧ φ ≠ 0 := by
    refine ⟨(∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (⟨1, by omega⟩ : Fin hyp.w2))
      - ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (⟨2, by omega⟩ : Fin hyp.w2), ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sub_mem _
        (Submodule.subset_span ⟨⟨1, by omega⟩, Fin.ne_of_val_ne (by simp), rfl⟩)
        (Submodule.subset_span ⟨⟨2, by omega⟩, Fin.ne_of_val_ne (by simp), rfl⟩)
    · -- support: difference of two `A₀`-supported diagonals
      intro z hz
      rw [ClassFunction.mem_support] at hz
      have hzsplit : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (⟨1, by omega⟩ : Fin hyp.w2))
            - (d : ℂ) • ζ) z ≠ 0 ∨
          ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (⟨2, by omega⟩ : Fin hyp.w2))
            - (d : ℂ) • ζ) z ≠ 0 := by
        rcases eq_or_ne (((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (⟨1, by omega⟩ : Fin hyp.w2))
            - (d : ℂ) • ζ) z) 0 with h1 | h1
        · refine Or.inr fun h2 => hz ?_
          rw [ClassFunction.sub_apply] at h1 h2 ⊢
          rw [ClassFunction.smul_apply] at h1 h2
          linear_combination h1 - h2
        · exact Or.inl h1
      rcases hzsplit with h | h
      · exact hDsupp ⟨1, by omega⟩ (Fin.ne_of_val_ne (by simp)) (ClassFunction.mem_support.mpr h)
      · exact hDsupp ⟨2, by omega⟩ (Fin.ne_of_val_ne (by simp)) (ClassFunction.mem_support.mpr h)
    · -- nonzero: pairing against `μ_1` gives `w₁ ≠ 0`
      intro h0
      have hip : ClassFunction.inner
          ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (⟨1, by omega⟩ : Fin hyp.w2))
            - ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (⟨2, by omega⟩ : Fin hyp.w2))
          (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (⟨1, by omega⟩ : Fin hyp.w2))
          = (hyp.w1 : ℂ) := by
        rw [ClassFunction.inner_sub_left,
          hyp.muColumnSum_inner hG hodd ⟨1, by omega⟩ ⟨1, by omega⟩,
          hyp.muColumnSum_inner hG hodd ⟨2, by omega⟩ ⟨1, by omega⟩,
          if_pos rfl, if_neg (Fin.ne_of_val_ne (by simp)), sub_zero]
      rw [h0, ClassFunction.inner_zero_left] at hip
      exact hw1C hip.symm
  -- (isometry) generator-level `⟨ν μ_j, ν μ_k⟩ = ⟨μ_j, μ_k⟩`, lifted to `ℤ[X]`
  have hXX : ∀ x ∈ Xc, ∀ y ∈ Xc,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y := by
    rintro x ⟨j, hj, rfl⟩ y ⟨k, hk, rfl⟩
    rw [hνcol j hj, hνcol k hk, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right,
      hyp.omegaSigmaColumnSum_inner hG hodd j k, hyp.muColumnSum_inner hG hodd j k]
    have hδδ : (δ : ℂ) * star (δ : ℂ) = 1 := by
      rcases hδpm with rfl | rfl <;> norm_num
    by_cases hjk : j = k
    · rw [if_pos hjk, ← mul_assoc, hδδ, one_mul]
    · rw [if_neg hjk, mul_zero, mul_zero]
  have hinner : ∀ φ ψ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) Xc →
      ψ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) Xc →
      ClassFunction.inner (ν φ) (ν ψ) = ClassFunction.inner φ ψ := fun φ ψ hφ hψ =>
    OddOrder.Peterfalvi.S07.mixed_inner_eq_on_zSpan_of_eq_on hXX φ hφ ψ hψ
  -- (τ-agreement) a supported column combination lies in `ℤ[D]` (coefficient sum `0`)
  have hextends : ∀ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) Xc hyp.A0 → ν φ = hyp.tau φ := by
    rintro φ ⟨hφspan, hφsupp⟩
    have hφspan' : φ ∈ Submodule.span ℤ (Set.range (fun jj : {j : Fin hyp.w2 // j ≠ 0} =>
        ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i jj.1)) := by
      rw [← hXc_range]; exact hφspan
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hφspan'
    have hc' : ∑ jj : {j : Fin hyp.w2 // j ≠ 0},
        c jj • (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i jj.1) = φ := hc
    -- `φ(1) = 0` since `1 ∉ A₀`
    have hφ1 : φ 1 = 0 := hsupp_val φ hφsupp 1 h1A0
    -- coefficient sum `0`
    have heval : (∑ jj : {j : Fin hyp.w2 // j ≠ 0}, (c jj : ℂ)) * ((hyp.w1 : ℂ) * (d : ℂ))
        = 0 := by
      rw [← hφ1, ← hc', ClassFunction.finset_sum_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun jj _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℂ (c jj), ClassFunction.smul_apply, hμ1 jj.1 jj.2]
    have hS0 : (∑ jj : {j : Fin hyp.w2 // j ≠ 0}, c jj) = 0 := by
      have hC : (∑ jj : {j : Fin hyp.w2 // j ≠ 0}, (c jj : ℂ)) = 0 :=
        (mul_eq_zero.mp heval).resolve_right (mul_ne_zero hw1C hdC)
      exact_mod_cast (by push_cast; exact hC :
        ((∑ jj : {j : Fin hyp.w2 // j ≠ 0}, c jj : ℤ) : ℂ) = 0)
    -- `φ = ∑ c_j·(μ_j − d·ζ) ∈ ℤ[D]`
    have hsplit : ∑ jj : {j : Fin hyp.w2 // j ≠ 0},
        c jj • ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i jj.1) - (d : ℂ) • ζ)
        = φ - (∑ jj : {j : Fin hyp.w2 // j ≠ 0}, c jj) • ((d : ℂ) • ζ) := by
      rw [← hc']
      simp only [smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [hS0, zero_smul, sub_zero] at hsplit
    have hφD : φ ∈ Submodule.span ℤ Dset := by
      rw [← hsplit]
      exact Submodule.sum_mem _ (fun jj _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨jj.1, jj.2, rfl⟩))
    exact OddOrder.Peterfalvi.S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on hDτ hφD
  -- (ZIrr) `ν(ℤ[X]) ⊆ ℤ[Irr G]`
  have hZIrr : ∀ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) Xc → ν φ ∈ ZIrr G := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, hj, rfl⟩ := hx
        rw [hνcol j hj, Int.cast_smul_eq_zsmul ℂ δ]
        exact Submodule.smul_mem _ δ (Submodule.sum_mem _ (fun i _ =>
          hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hodd i j))
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul a x _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ a ih
  -- (mixed isometry) `⟨ν μ_j, ν η⟩ = 0 = ⟨μ_j, η⟩` by (5.3.b)
  have hmixed : ∀ x ∈ Xc, ∀ y ∈ hyp.SHCSet,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y := by
    rintro x ⟨j, hj, rfl⟩ y hy
    rw [hνcol j hj, hνY y hy, hXY _ ⟨j, hj, rfl⟩ y hy, ClassFunction.inner_smul_left]
    have hyne : y.conj ≠ y := fun hcon =>
      inducedFamily_hasNoRealCharacters hModd hy.1 hcon
    have h0 : ClassFunction.inner (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j)
        (coh.extension y) = 0 := by
      rw [inner_sum_left]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [OddOrder.RepresentationTheory.inner_conj_symm,
        hyp.SHC_extension_inner_alignedOmegaSigma_eq_zero hG coh hodd hy.1 hy.2.1 hy.2.2 hyne i j,
        star_zero]
    rw [h0, mul_zero]
  -- (generation) `ℤ[X ∪ S₁, A₀] ⊆ ℤ[ℤ[X, A₀] ∪ ℤ[S₁, A₀] ∪ D]`
  have hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) (Xc ∪ hyp.SHCSet) hyp.A0 ⊆
      (Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) Xc hyp.A0 ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) hyp.SHCSet hyp.A0 ∪ Dset) :
          Set (ClassFunction ↥M ℂ)) := by
    rintro φ ⟨hφspan, hφsupp⟩
    have hφsup : φ ∈ Submodule.span ℤ Xc ⊔ Submodule.span ℤ hyp.SHCSet := by
      rw [← Submodule.span_union]; exact hφspan
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hφsup
    rw [hXc_range] at hu
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hu
    have hc' : ∑ jj : {j : Fin hyp.w2 // j ≠ 0},
        c jj • (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i jj.1) = u := hc
    -- the diagonal part `ψ = ∑ c_j·(μ_j − d·ζ) ∈ ℤ[D]`
    set ψ : ClassFunction ↥M ℂ := ∑ jj : {j : Fin hyp.w2 // j ≠ 0},
      c jj • ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i jj.1) - (d : ℂ) • ζ) with hψ_def
    have hψD : ψ ∈ Submodule.span ℤ Dset :=
      Submodule.sum_mem _ (fun jj _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨jj.1, jj.2, rfl⟩))
    have hψsplit : ψ = u - (∑ jj : {j : Fin hyp.w2 // j ≠ 0}, c jj) • ((d : ℂ) • ζ) := by
      rw [hψ_def, ← hc']
      simp only [smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    -- the `S₁`-side remainder `r = φ − ψ = v + (∑c)·d·ζ`, supported on `A₀`
    have hrY : φ - ψ ∈ Submodule.span ℤ hyp.SHCSet := by
      rw [hψsplit, ← huv]
      have hre : u + v - (u - (∑ jj : {j : Fin hyp.w2 // j ≠ 0}, c jj) • ((d : ℂ) • ζ))
          = v + (∑ jj : {j : Fin hyp.w2 // j ≠ 0}, c jj) • ((d : ℂ) • ζ) := by
        abel
      rw [hre]
      refine Submodule.add_mem _ hv ?_
      rw [Nat.cast_smul_eq_nsmul ℂ d ζ, ← natCast_zsmul ζ d, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hζSHC)
    have hψsupp : ∀ z, z ∉ hyp.A0 → ψ z = 0 := by
      intro z hz
      rw [hψ_def, ClassFunction.finset_sum_apply]
      refine Finset.sum_eq_zero fun jj _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℂ (c jj), ClassFunction.smul_apply,
        hsupp_val _ (hDsupp jj.1 jj.2) z hz, mul_zero]
    have hrsupp : (φ - ψ).support ⊆ hyp.A0 := by
      intro z hzsup
      by_contra hz
      rw [ClassFunction.mem_support, ClassFunction.sub_apply,
        hsupp_val φ hφsupp z hz, hψsupp z hz, sub_zero] at hzsup
      exact hzsup rfl
    -- assemble `φ = ψ + (φ − ψ)`
    have hφ_eq : φ = ψ + (φ - ψ) := by abel
    rw [hφ_eq]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.span_mono Set.subset_union_right hψD
    · exact Submodule.subset_span (Or.inl (Or.inr ⟨hrY, hrsupp⟩))
  -- ### assembly: `S = X ∪ S₁` and the union engine
  have hSeq : hyp.Sset = Xc ∪ hyp.SHCSet := by
    ext φ
    constructor
    · intro hφ
      rcases hstruct φ hφ with h | ⟨j, hj, rfl⟩
      · exact Or.inr h
      · exact Or.inl ⟨j, hj, rfl⟩
    · rintro (⟨j, hj, rfl⟩ | h)
      · refine hyp.muGrid_column_sum_mem_inducedFamily hG hodd j ?_
        rw [hdeg 0 j hj]
        intro hone
        have hd1 : d = 1 := by exact_mod_cast hone
        omega
      · exact h.1
  rw [hSeq]
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    ⟨hnonzero, ν, hinner, hextends, hZIrr⟩ coh ν (fun x _ => rfl) hνY
    (OddOrder.Peterfalvi.S08.inner_eq_zero_of_mem_span_of_pairwise_orthogonal hXY)
    hmixed Dset hDτ hgen

end OddOrder.Peterfalvi.S12


