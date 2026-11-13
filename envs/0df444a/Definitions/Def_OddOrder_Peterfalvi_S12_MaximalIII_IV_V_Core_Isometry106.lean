-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Isometry106
-- name    : OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Isometry106
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:44:46.441198+00:00
-- url     : https://prove2.me/theorems/3bc7e95a-432f-4c69-89db-1cfd42a5570f
-- title:
--   Peterfalvi (10.5)–(10.6): Dade isometry calculations, part 2 (Isometry106)
-- statement:
--   A continuation of the Dade-isometry calculations in §10, covering the inner-product computations for the coherent extension $\tau_1$ in Peterfalvi (10.5) and (10.6).
--
--   Main declarations: `Hypothesis.muGridAlpha_tau1_inner_muColumn_self_sub_conj` (Peterfalvi (10.6)(a), `(α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = 1`); `Hypothesis.muColumn_tau1_inner_self` (Peterfalvi (10.5), `‖μ_k^{τ₁}‖² = w₁`); `Hypothesis.muGridAlpha_tau_mem_ZIrr` (§10 `α_{ij}^τ` is a virtual character of `G`); `Hypothesis.muGridAlpha_tau1_zeta_eq_neg_n` (Peterfalvi (10.5), `a = 0`).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/Isometry106.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/Isometry106.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Isometry105

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a), `(α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = 1`** (diagonal): the coherent-side
form of the G-side diagonal inner product `muGridAlpha_tau_inner_muColumn_self_sub_conj`.  Since
`μ_j = ∑_i μ_{ij} ∈ S` (`muGrid_column_sum_mem_inducedFamily`) and `ζ̄ ∈ S`, the supported
combination `(μ_j − dζ̄)^τ` splits as `μ_j^{τ₁} − dζ̄^{τ₁}` (`tau_muColumn_sub_conj_eq_tau1`).

This is the reduction opening `1 = (α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁})` of Peterfalvi (10.6)(a);
dropping the `⊥ Im σ` terms (`ζ^{τ₁}, ζ̄^{τ₁} ⊥ Im σ`, `ζ^{τ₁} ⊥ μ_j^{τ₁}`) gives
`(δ(ω_{ij}^σ − ω_{i0}^σ), μ_j^{τ₁}) = 1`, and Peterfalvi (5.8) then yields the summed isometry
`μ_j^{τ₁} = δ∑_i ω_{ij}^σ` (the (10.6)(a) conclusion, still gated on (5.8)). -/
theorem Hypothesis.muGridAlpha_tau1_inner_muColumn_self_sub_conj [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 = (d : ℂ))
    (hdj1 : hyp.muGrid hG hodd 0 j 1 ≠ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j)
          - (d : ℂ) • coh.tau1 ζ.conj) = 1 := by
  have hG_side := hyp.muGridAlpha_tau_inner_muColumn_self_sub_conj hG hodd i hj0 hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj h0ζ hjζ hcol1
  rwa [hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd j coh hζS hζirr hcol1 hζ1 hdj1] at hG_side

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖μ_k^{τ₁}‖² = w₁`** (`0 < k < w₂`): the coherent extension `τ₁` is an
isometry on `ℤ[S]`, and `μ_k = ∑_i μ_{ik} ∈ S` (`muGrid_column_sum_mem_inducedFamily`), so
`‖μ_k^{τ₁}‖² = ‖μ_k‖² = w₁` (`coherent.extension_inner_eq` + `muGrid_column_sum_inner_self`).

This is the `‖μ_k^{τ₁}‖²` factor of the (10.5) Cauchy–Schwarz bound
`d²a² = (α_{ij}^τ, μ_k^{τ₁})² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖² = (2+n²)w₁`. -/
theorem Hypothesis.muColumn_tau1_inner_self [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    ClassFunction.inner (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k))
        (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = (hyp.w1 : ℂ) := by
  have hμkS := hyp.muGrid_column_sum_mem_inducedFamily hG hodd k hdk1
  have hspan : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hμkS
  change ClassFunction.inner (coh.coherent.extension (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k))
      (coh.coherent.extension (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = (hyp.w1 : ℂ)
  rw [coh.coherent.extension_inner_eq _ _ hspan hspan]
  exact hyp.muGrid_column_sum_inner_self hG hodd k

open scoped FiniteInduce in
/-- **§10 `α_{ij}^τ` is a virtual character of `G`** (Peterfalvi (10.5)): `α_{ij} = μ_{ij} −
δ·μ_{i0}
−
n·ζ` is a virtual character of `M` (`muGrid_isIrreducible`, `ζ` irreducible) and is `A_0`-supported
(`muGrid_alpha_support`), so its Dade image lies in `ℤ[Irr G]`
(`dadeIntegralCharacterMap_mem_ZIrr_of_supported`).  Together with `ζ^{τ₁}, μ_k^{τ₁} ∈ ℤ[Irr G]`
this
makes the inner products of the `a = 0` argument integers. -/
theorem Hypothesis.muGridAlpha_tau_mem_ZIrr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin
        hyp.w2}
    (hj0 : j ≠ 0) {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ∈ ZIrr G := by
  have := hyp.finiteG
  have hαZ : (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ∈ ZIrr ↥M :=
      by
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (hyp.muGrid_isIrreducible hG hodd i j).mem_ZIrr
        ?_) ?_
    · rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (hyp.muGrid_isIrreducible hG hodd i 0).mem_ZIrr δ
    · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hζirr.mem_ZIrr n
  have hsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dadeData.dade hsupp hαZ

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `a = 0`**: the integer `a = (α_{ij}^τ, ζ^{τ₁}) + n` of the (10.5) Cauchy–
Schwarz argument vanishes, i.e. `(α_{ij}^τ, ζ^{τ₁}) = −n`.

`(α_{ij}^τ, ζ^{τ₁}) = m ∈ ℤ` (`α_{ij}^τ, ζ^{τ₁} ∈ ℤ[Irr G]`, `inner_mem_ZIrr_int`); set `a = m + n`.
Then `(α_{ij}^τ, μ_k^{τ₁}) = da` (`muGridAlpha_tau1_inner_muColumn`), and Cauchy–Schwarz
(`classFunction_inner_re_sq_le`) with `‖α_{ij}^τ‖² = 2 + n²` (`muGridAlpha_tau_inner_self`) and
`‖μ_k^{τ₁}‖² = w₁` (`muColumn_tau1_inner_self`) gives `(da)² ≤ (2+n²)w₁`.  By the numeric core
(`cauchySchwarz_numeric`; `d = nw₁+δ`, `δ = ±1`, `w₁ ≥ 3` odd, `n ≥ 2` even) this forces `a = 0`. -/
theorem Hypothesis.muGridAlpha_tau1_zeta_eq_neg_n [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ hyp.w1) (hn2 : 2 ≤ n) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.tau1 ζ) = -(n : ℂ) := by
  have := hyp.finiteG
  classical
  -- `(α^τ, ζ^{τ₁}) = m ∈ ℤ`.
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hζZ : coh.tau1 ζ ∈ ZIrr G := coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hαZ hζZ
  -- `(α^τ, μ_k^{τ₁}) = d·(m + n)` and the two norms.
  have hda := hyp.muGridAlpha_tau1_inner_muColumn hG hodd i hj0 k hjk hk0 coh hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1 hdk1
  rw [hm] at hda
  have hnorm_a := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  have hnorm_mu := hyp.muColumn_tau1_inner_self hG hodd k coh hdk1
  -- Cauchy–Schwarz, with the three inner products substituted.
  have hcs := classFunction_inner_re_sq_le
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
    (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k))
  rw [hda, hnorm_a, hnorm_mu] at hcs
  have hre1 : ((d : ℂ) * ((m : ℂ) + (n : ℂ))).re = (d : ℝ) * ((m : ℝ) + (n : ℝ)) := by
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  have hre2 : ((2 : ℂ) + (n : ℂ) ^ 2).re = 2 + (n : ℝ) ^ 2 := by
    simp [Complex.add_re, pow_two, Complex.mul_re]
  rw [hre1, hre2, Complex.natCast_re] at hcs
  -- Apply the numeric core with `a = m + n`.
  have ha0 : m + (n : ℤ) = 0 := by
    refine cauchySchwarz_numeric (d := d) (n := n) (w₁ := hyp.w1) (δ := δ) (a := m + n)
      (by linarith [hnf]) hδpm hw1 hn2 ?_
    push_cast
    convert hcs using 2
  rw [hm]
  have hmn : m = -(n : ℤ) := by omega
  rw [hmn]; push_cast; ring

open scoped FiniteInduce in
/-- **§10 `‖ζ^{τ₁}‖² = 1`** (Peterfalvi (10.5)): the coherent extension `τ₁` is an isometry on
`ℤ[S]` and `ζ ∈ S` is irreducible, so `‖ζ^{τ₁}‖² = ‖ζ‖² = 1`. -/
theorem Hypothesis.zeta_tau1_inner_self [Finite G] {M : Subgroup G}
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (_hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ) = 1 := by
  have hspan : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  change ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ) = 1
  rw [coh.coherent.extension_inner_eq _ _ hspan hspan,
    OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]

open scoped FiniteInduce in
/-- **`ζ^{τ₁} ⊥ μ_k^{τ₁}`** (Peterfalvi (10.6)(a) reduction): the coherent image of the degree-`w₁`
irreducible `ζ` is orthogonal to that of the column character `μ_k = ∑_i μ_{ik} ∈ 𝒮`.  By the
isometry, `(ζ^{τ₁}, μ_k^{τ₁}) = (ζ, ∑_i μ_{ik}) = ∑_i (ζ, μ_{ik}) = 0`, each summand `0` by the
degree mismatch `μ_{ik}(1) = d ≠ w₁ = ζ(1)` (`muGrid_inner_eq_zero_of_apply_one_ne` + conjugate
symmetry).  A second orthogonality of the (10.6)(a) reduction (see `zeta_tau1_inner_conj`). -/
theorem Hypothesis.zeta_tau1_inner_muColumn [Finite G] {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    ClassFunction.inner (coh.tau1 ζ)
        (coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = 0 := by
  have hμkS := hyp.muGrid_column_sum_mem_inducedFamily hG hodd k hdk1
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  have hspanμ : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hμkS
  change ClassFunction.inner (coh.coherent.extension ζ)
    (coh.coherent.extension (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)) = 0
  rw [coh.coherent.extension_inner_eq _ _ hspanζ hspanμ,
    OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have h0 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i k hζirr (hkζ i)
  rw [OddOrder.RepresentationTheory.inner_conj_symm, h0, star_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖X‖² = 2` and `X ⊥ ζ^{τ₁}`** where `X = α_{ij}^τ + n·ζ^{τ₁}`: with
`(α_{ij}^τ, ζ^{τ₁}) = −n` (`a = 0`, `muGridAlpha_tau1_zeta_eq_neg_n`), `‖α_{ij}^τ‖² = 2 + n²`
(`muGridAlpha_tau_inner_self`) and `‖ζ^{τ₁}‖² = 1` (`zeta_tau1_inner_self`):
`(X, ζ^{τ₁}) = (α_{ij}^τ, ζ^{τ₁}) + n‖ζ^{τ₁}‖² = −n + n = 0`, and
`‖X‖² = ‖α_{ij}^τ‖² + 2n·(α_{ij}^τ, ζ^{τ₁}) + n²‖ζ^{τ₁}‖² = (2+n²) − 2n² + n² = 2`.

So `α_{ij}^τ = X − n·ζ^{τ₁}` with `X` a virtual character of `G` orthogonal to `ζ^{τ₁}` of squared
norm `2` — the decomposition the (10.5) `(v)`/`(vi)` argument (`NC(ψ) ≤ 4`, (3.8)) operates on. -/
theorem Hypothesis.muGridAlpha_tau_X_inner [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ hyp.w1) (hn2 : 2 ≤ n) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ) (coh.tau1 ζ) = 0
    ∧ ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ)
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ) = 2 := by
  have ha0 := hyp.muGridAlpha_tau1_zeta_eq_neg_n hG hodd i hj0 k hjk hk0 coh hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1 hdk1 hδpm hw1 hn2
  have hnorm_a := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  have hzz := hyp.zeta_tau1_inner_self hG hodd coh hζS hζirr
  have ha0' : ClassFunction.inner (coh.tau1 ζ)
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)) = -(n :
          ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, ha0, star_neg, star_natCast]
  constructor
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_smul_left, ha0, hzz, mul_one]
    ring
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      ha0, ha0', hnorm_a, hzz, star_natCast, mul_one]
    ring

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), (vi) precursor — `ψ` vanishes on `V`**: the virtual character
`ψ = α_{ij}^τ + n·ζ^{τ₁} − δ(ω_{ij}^σ − ω_{i0}^σ)` (this is `X − δ(ω^σ diff)` of the (10.5) endgame,
since `α^τ = X − nζ^{τ₁}`) vanishes on `V`.

Combines the value-on-`V` leg `tau_muGridAlpha_apply_eq_on_typePV` (`α^τ = δ(ω^σ diff)` on `V`, by
(3.2.c)/(4.3.c) and the definition of `τ`) with the vanishing of `ζ^{τ₁}` on `V` (`hζvanish`, the
§5/§7 input of (10.5): "By (5.3.b), (5.5) and (3.2.d), `ζ^{τ₁}` vanishes on `V`").  The remaining
step to `alpha_tau_image` is `NC(ψ) ≤ 4 < 2·inf(w₁,w₂)` + Theorem (3.8)
(`S05.sigmaCoeff_trichotomy`, requiring a `FullDadeApplication` for the type-`P`
`TICyclicHypothesis`)
forcing `ψ ⊥ ω^σ`, hence `ψ = 0`. -/
theorem Hypothesis.muGridPsi_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {i : Fin hyp.w1} {j : Fin hyp.w2} (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hζvanish : ∀ v ∈ typePV M hyp.typeP, coh.tau1 ζ v = 0)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        + (n : ℂ) • coh.tau1 ζ
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
            - hyp.alignedOmegaSigmaGrid hG hodd i 0)) v = 0 := by
  have hleg := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj hζS hdeg hμ0 hζ1 hnf hδj hv
  simp only [ClassFunction.sub_apply, ClassFunction.add_apply, ClassFunction.smul_apply] at hleg ⊢
  rw [hleg, hζvanish v hv]
  simp

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(ζ − ζ̄)^τ` vanishes on `V`** (the "by definition of `τ`" step underlying
the (5.3.b)/(5.5)/(3.2.d) `ζ^{τ₁}`-vanishing argument).  Since `ζ` is induced from the normal
`M' = [M,M]` and every `v ∈ V = typePV` lies outside `M'` (`typePData_typePV_not_mem_derived`),
both `ζ` and its conjugate `ζ̄` vanish at `v`; the difference `ζ − ζ̄` is `A_0(M)`-supported
(`zeta_sub_conj_support`), so the Dade isometry restores its value at `v`
(`tau_apply_of_mem_typePV`), giving `(ζ − ζ̄)^τ(v) = 0`. -/
theorem Hypothesis.tau_zeta_sub_conj_vanishes_on_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    hyp.tau (ζ - ζ.conj) v = 0 := by
  have := hyp.finiteG
  classical
  have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
  have hsupp := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  rw [hyp.tau_apply_of_mem_typePV hsupp hv hvM]
  -- `ζ` (induced from the normal `M'`) vanishes at `v ∉ M'`, hence so does `ζ̄ = star ∘ ζ`.
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hv
  have hζv : ζ ⟨v, hvM⟩ = 0 := by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
  rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hζv, star_zero, sub_zero]

open scoped FiniteInduce in
/-- **`(χ − χ̄)^τ` is orthogonal to every aligned `σ`-grid entry** (Peterfalvi (5.3.b),
generalised from `ζ` to any irreducible member of `S`): the difference image vanishes on `V`
(`tau_zeta_sub_conj_vanishes_on_typePV`), lies in `ℤ[Irr G]` with norm `2`, so by the
`(3.7)/(3.8)` all-zero trichotomy (`sigmaCoeff_eq_zero_of_vanishOnV`) every `σ`-coefficient —
in particular every `⟨·, ω_{ik}^σ⟩` — vanishes.  This is the (5.2.e) member-vs-column
orthogonality core (issue 2022). -/
theorem Hypothesis.tau_chidiff_inner_alignedOmega_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {χ : ClassFunction ↥M ℂ}
    (hχS : χ ∈ inducedFamily M) (hχirr : IsIrreducibleCharacter χ)
    (i : Fin hyp.w1) (k : Fin hyp.w2) :
    ClassFunction.inner (hyp.tau (χ - χ.conj))
      (hyp.alignedOmegaSigmaGrid hG hodd i k) = 0 := by
  have := hyp.finiteG
  classical
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  -- `T`-facts
  have hχcS : χ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hχS
  have hχcirr : IsIrreducibleCharacter χ.conj := hχirr.conj
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hχne : χ.conj ≠ χ := inducedFamily_hasNoRealCharacters hModd hχS
  have hvanish : ∀ w ∈ tic.V, hyp.tau (χ - χ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hχS hχirr hw
  have hsupp := hyp.zeta_sub_conj_support hG hodd hχS hχirr
  have hTZ : hyp.tau (χ - χ.conj) ∈ ZIrr G := by
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hsupp ?_
    exact Submodule.sub_mem _ hχirr.mem_ZIrr hχcirr.mem_ZIrr
  have hT2 : ClassFunction.inner (hyp.tau (χ - χ.conj)) (hyp.tau (χ - χ.conj)) = 2 := by
    have hset : ∀ s ∈ ({χ - χ.conj} : Set (ClassFunction ↥M ℂ)), s.support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
      rintro s rfl
      exact hsupp
    have hmem : χ - χ.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
        ({χ - χ.conj} : Set (ClassFunction ↥M ℂ)) := Submodule.subset_span rfl
    have hpres := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      hyp.dadeData.dade hset hmem hmem
    rw [show hyp.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData) from rfl, hpres,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right]
    have h11 : ClassFunction.inner χ χ = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨χ, hχirr⟩ : IrreducibleCharacter ↥M) ⟨χ, hχirr⟩
    have hcc : ClassFunction.inner χ.conj χ.conj = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨χ.conj, hχcirr⟩ : IrreducibleCharacter ↥M) ⟨χ.conj, hχcirr⟩
    have hcross : ClassFunction.inner χ χ.conj = 0 :=
      inducedFamily_pairwiseOrthogonal hχS hχcS (Ne.symm hχne)
    have hcross' : ClassFunction.inner χ.conj χ = 0 :=
      inducedFamily_pairwiseOrthogonal hχcS hχS hχne
    rw [h11, hcc, hcross, hcross']
    ring
  -- engine + `P`-enumeration
  have hall := tic.sigmaCoeff_eq_zero_of_vanishOnV hVeq app hTZ hT2 hvanish
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  have hk := hall (P k)
  rw [show tic.sigmaCoeff hVeq app (hyp.tau (χ - χ.conj)) (P k)
      = ClassFunction.inner (hyp.tau (χ - χ.conj)) (tic.chiFam hVeq app (P k)) from rfl,
    ← hP k] at hk
  exact hk

/-- **Norm-`1` projection orthogonality.**  If `a, s ∈ ℤ[Irr G]` with `‖a‖² = ‖b‖² = ‖s‖² = 1`,
`a ⊥ b`, and the difference `a − b` is orthogonal to `s`, then `a ⊥ s`.

Since `⟨a,s⟩ = ⟨b,s⟩ =: x ∈ ℤ` (`a, s ∈ ℤ[Irr G]`, `inner_mem_ZIrr_int`), the projection norm
`‖s − x·a − x·b‖² = 1 − 2x² ≥ 0` forces `2x² ≤ 1`, hence `x = 0`.  This is the integral-geometry
core that lets the §10 `ζ^{τ₁}`-vanishing argument bypass the (5.4)/(5.5) `R(ζ)` machinery:
applied with `a = ζ^{τ₁}`, `b = ζ̄^{τ₁}`, `s = ω^σ`, the orthogonality of `(ζ − ζ̄)^τ = a − b` to
the
`σ`-image (Peterfalvi (5.3.b), via (3.8)) gives `ζ^{τ₁} ⊥ ω^σ` directly. -/
theorem inner_left_eq_zero_of_inner_sub_eq_zero {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {a b s : ClassFunction G ℂ} (haZ : a ∈ ZIrr G) (hsZ : s ∈ ZIrr G)
    (ha1 : ClassFunction.inner a a = 1) (hb1 : ClassFunction.inner b b = 1)
    (hs1 : ClassFunction.inner s s = 1) (hab : ClassFunction.inner a b = 0)
    (hdiff : ClassFunction.inner (a - b) s = 0) :
    ClassFunction.inner a s = 0 := by
  obtain ⟨x, hx⟩ := ClassFunction.inner_mem_ZIrr_int haZ hsZ
  -- `⟨b,s⟩ = ⟨a,s⟩ = x` from `⟨a − b, s⟩ = 0`.
  have hbs : ClassFunction.inner b s = (x : ℂ) := by
    rw [ClassFunction.inner_sub_left, hx, sub_eq_zero] at hdiff
    exact hdiff.symm
  -- the conjugate-symmetric companions (`x` is real, being an integer).
  have hsa : ClassFunction.inner s a = (x : ℂ) := by
    rw [inner_conj_symm a s, hx, star_intCast]
  have hsb : ClassFunction.inner s b = (x : ℂ) := by
    rw [inner_conj_symm b s, hbs, star_intCast]
  have hba : ClassFunction.inner b a = 0 := by
    rw [inner_conj_symm a b, hab, star_zero]
  -- the projection norm `‖s − x·a − x·b‖² = 1 − 2x²`.
  have key : ClassFunction.inner (s - (x : ℂ) • a - (x : ℂ) • b)
      (s - (x : ℂ) • a - (x : ℂ) • b) = 1 - 2 * (x : ℂ) ^ 2 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      ha1, hb1, hs1, hab, hba, hx, hbs, hsa, hsb, star_intCast]
    ring
  have hnn := inner_self_re_nonneg (s - (x : ℂ) • a - (x : ℂ) • b)
  rw [key] at hnn
  have hcast : (1 : ℂ) - 2 * (x : ℂ) ^ 2 = ((1 - 2 * x ^ 2 : ℤ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.intCast_re] at hnn
  have hint : (0 : ℤ) ≤ 1 - 2 * x ^ 2 := by exact_mod_cast hnn
  have h0 : (0 : ℤ) ≤ x ^ 2 := sq_nonneg x
  have hsq : x ^ 2 = 0 := by omega
  have hx0 : x = 0 := by rw [pow_two] at hsq; exact mul_self_eq_zero.mp hsq
  rw [hx, hx0, Int.cast_zero]

open scoped FiniteInduce in
/-- **Per-element orthogonality of a difference-image family** (Peterfalvi (5.5)-style upgrade):
if `s` is a norm-`1` virtual character orthogonal to the *sum* `(χ−χ̄)^τ = ∑ R(χ)`, then `s` is
orthogonal to each element of `R(χ)`.  With `β := T − α` (the complementary part), `α − (−β) = T`
and the norm-`1` projection lemma applies. -/
theorem OrthonormalCharacterImageFamily.elt_inner_eq_zero {M : Subgroup G} [Finite G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥M : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G} {χ : ClassFunction ↥M ℂ}
    (R : OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily τ χ)
    {α : ClassFunction G ℂ} (hα : α ∈ R.imageSet)
    {s : ClassFunction G ℂ} (hsZ : s ∈ ZIrr G)
    (hs1 : ClassFunction.inner s s = 1)
    (hT2 : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) = 2)
    (hTs : ClassFunction.inner (τ (χ - χ.conj)) s = 0) :
    ClassFunction.inner α s = 0 := by
  classical
  set T := τ (χ - χ.conj) with hT
  have hTsum : T = ∑ β ∈ R.imageSet, β := R.image_eq
  have hαZ : α ∈ ZIrr G := R.mem_ZIrr α hα
  have hα1 : ClassFunction.inner α α = 1 := by
    have := R.orthonormal α hα α hα
    rwa [if_pos rfl] at this
  have hTZ : T ∈ ZIrr G := by
    rw [hTsum]
    exact Submodule.sum_mem _ fun β hβ => R.mem_ZIrr β hβ
  have hαT : ClassFunction.inner α T = 1 := by
    rw [hTsum, OddOrder.RepresentationTheory.inner_sum_right, Finset.sum_eq_single α]
    · rw [hα1]
    · intro β hβ hne
      have := R.orthonormal α hα β hβ
      rwa [if_neg (fun h => hne h.symm)] at this
    · intro habs
      exact absurd hα habs
  -- `b := −(T − α)`; then `α − b = T`
  set b : ClassFunction G ℂ := -(T - α) with hb
  have hbZ : b ∈ ZIrr G := by
    rw [hb]
    exact Submodule.neg_mem _ (Submodule.sub_mem _ hTZ hαZ)
  have hbb : ClassFunction.inner b b = 1 := by
    have hexp : ClassFunction.inner (T - α) (T - α)
        = ClassFunction.inner T T - ClassFunction.inner T α
          - ClassFunction.inner α T + ClassFunction.inner α α := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right]
      ring
    have hTα : ClassFunction.inner T α = 1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hαT]
      norm_num
    rw [hb, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg,
      hexp, hT2, hTα, hαT, hα1]
    ring
  have hαb : ClassFunction.inner α b = 0 := by
    have hTα : ClassFunction.inner α (T - α) = 0 := by
      rw [ClassFunction.inner_sub_right, hαT, hα1]
      ring
    rw [hb, ClassFunction.inner_neg_right, hTα, neg_zero]
  have hdiff : ClassFunction.inner (α - b) s = 0 := by
    have : α - b = T := by
      rw [hb]
      abel
    rw [this]
    exact hTs
  exact inner_left_eq_zero_of_inner_sub_eq_zero hαZ hsZ hα1 hbb hs1 hαb hdiff

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `ζ^{τ₁}` vanishes on `V`** (the genuine §5/§7 input, the textbook's
"By (5.3.b), (5.5) and (3.2.d), `ζ^{τ₁}` vanishes on `V`").

Reorganized to avoid the (5.4)/(5.5) `R(ζ)`-extraction machinery, using the integral norm-`1`
projection (`inner_left_eq_zero_of_inner_sub_eq_zero`) instead:
* `(ζ − ζ̄)^τ = ζ^{τ₁} − ζ̄^{τ₁}` vanishes on `V` (`tau_zeta_sub_conj_vanishes_on_typePV`) and has
  `NC ≤ 2 < min(w₁, w₂)`: each of `ζ^{τ₁}`, `ζ̄^{τ₁}` is a norm-`1` virtual character with at most
  one nonzero `σ`-coefficient (`ncard_inner_chiFam_ne_zero_le_one`), so by the (3.8) corollary
  `sigmaCoeff_eq_zero_of_sigmaNC_lt` every `σ`-coefficient of `(ζ − ζ̄)^τ` vanishes (Peterfalvi
  (5.3.b));
* `ζ^{τ₁}, ζ̄^{τ₁}` are orthonormal norm-`1` virtual characters (coherence isometry on `ℤ[S]`), so
  the projection lemma upgrades `⟨ζ^{τ₁} − ζ̄^{τ₁}, χ_{pq}⟩ = 0` to `⟨ζ^{τ₁}, χ_{pq}⟩ = 0`
  (Peterfalvi (5.5));
* orthogonality to every `χ_{pq} = ω_{pq}^σ` forces `ζ^{τ₁}` to vanish on `V` (Peterfalvi (3.2.d),
  `eq_zero_of_mem_V_of_inner_chiFam_eq_zero`).

This is the last analytic input of the (10.5) Dade-image identity; with the value-on-`V` leg it
gives `ψ = X − δ(ω^σ diff)` vanishing on `V` (`muGridPsi_vanishes_on_typePV`), unconditionally. -/
theorem Hypothesis.tau1_zeta_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    coh.tau1 ζ v = 0 := by
  have := hyp.finiteG
  classical
  -- the §5 `G`-level TI-cyclic hypothesis + Dade application (the ready (10.5) `σ` pattern).
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData⟩
  have hVeq : tic.V = tic.Vdiff := rfl
  -- `ζ̄ ∈ S` irreducible; the `τ₁`-images are orthonormal norm-`1` virtual characters of `G`.
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have haZ : coh.tau1 ζ ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  have hbZ : coh.tau1 ζ.conj ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ.conj (Submodule.subset_span hζcS)
  have ha1 : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζS hζirr
  have hb1 : ClassFunction.inner (coh.tau1 ζ.conj) (coh.tau1 ζ.conj) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζcS hζcirr
  have hab : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ.conj) = 0 := by
    change ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ.conj) = 0
    rw [coh.coherent.extension_inner_eq _ _ (Submodule.subset_span hζS)
        (Submodule.subset_span hζcS),
      OddOrder.RepresentationTheory.irr_cf_inner hζirr hζcirr, if_neg (fun h => hζne h.symm)]
  -- `(ζ − ζ̄)^τ` vanishes on `V`, with `NC ≤ 2 < min(w₁, w₂)`.
  have hvanish : ∀ w ∈ tic.V, hyp.tau (ζ - ζ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hζS hζirr hw
  have hNC : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
      < min (Nat.card ↥tic.W1) (Nat.card ↥tic.W2) := by
    have hbound : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj)) ≤ 2 := by
      have hsub : {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0} ⊆
          {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0} := by
        intro pq hpq
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
        apply hpq
        change ClassFunction.inner (hyp.tau (ζ - ζ.conj)) (tic.chiFam hVeq app pq) = 0
        rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr,
          ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
      calc tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
          = {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0}.ncard := rfl
        _ ≤ ({pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
              {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0}.ncard +
              {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0}.ncard :=
            Set.ncard_union_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hbZ hb1
        _ = 2 := rfl
    have h3a := tic.three_le_card_W1
    have h3b := tic.three_le_card_W2
    omega
  -- (3.2.d): orthogonality to every `χ_{pq}` forces vanishing on `V`.
  refine tic.eq_zero_of_mem_V_of_inner_chiFam_eq_zero hVeq app (fun a' b' => ?_) hv
  have hL3 : tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) (a', b') = 0 :=
    tic.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hvanish hNC (a', b')
  have hdiff : ClassFunction.inner (coh.tau1 ζ - coh.tau1 ζ.conj)
      (tic.chiFam hVeq app (a', b')) = 0 := by
    rw [← hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr]; exact hL3
  have hsZ : tic.chiFam hVeq app (a', b') ∈ ZIrr G := (tic.chiFam_spec hVeq app).2.1 (a', b')
  have hs1 : ClassFunction.inner (tic.chiFam hVeq app (a', b'))
      (tic.chiFam hVeq app (a', b')) = 1 := by
    rw [(tic.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  exact inner_left_eq_zero_of_inner_sub_eq_zero haZ hsZ ha1 hb1 hs1 hab hdiff

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), Dade-image half (grid level)**: the genuine `μ`-grid statement of the
Dade-image identity, `α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`, with `ω^σ` the *aligned*
`σ`-grid `alignedOmegaSigmaGrid` and `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ`.

This is the full (10.5) endgame.  Writing `X = α_{ij}^τ + n·ζ^{τ₁}`, the goal reduces to
`X = δ·(ω_{ij}^σ − ω_{i0}^σ)`.  Now `X` is a virtual character of `G` with `‖X‖² = 2`
(`muGridAlpha_tau_X_inner`), the aligned `σ`-grid entries are members `χ_{P_{ij}}` of the
orthonormal `σ`-image family (`exists_alignedOmegaSigmaGrid_chiFam_family`), and the difference
`X − δ·(ω_{ij}^σ − ω_{i0}^σ)` vanishes on `V` (`muGridPsi_vanishes_on_typePV` together with the
`ζ^{τ₁}`-vanishing `tau1_zeta_vanishes_on_typePV`).  The norm-`2` Dade-image trichotomy
`eq_smul_chiFam_diff_of_vanishOnV` (the §5 generalisation of the §6 `(4.8)` endgame) then forces
`X = δ·(χ_{P_{ij}} − χ_{P_{i0}})`.  (`alpha_tau_image` is the thin `CharacterParameters`
corollary.) -/
theorem Hypothesis.tau_muGridAlpha_eq [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ hyp.w1) (hn2 : 2 ≤ n) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - (n : ℂ) • coh.tau1 ζ := by
  have := hyp.finiteG
  classical
  -- `X = α_{ij}^τ + n·ζ^{τ₁}` has `‖X‖² = 2` and lies in `ℤ[Irr G]`.
  have hXfacts := hyp.muGridAlpha_tau_X_inner hG hodd i hj0 k hjk hk0 coh hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1 hdk1 hδpm hw1 hn2
  have hτ1ζZ : coh.tau1 ζ ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hXZ : hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      + (n : ℂ) • coh.tau1 ζ ∈ ZIrr G := by
    refine Submodule.add_mem _ hαZ ?_
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hτ1ζZ n
  -- the aligned `σ`-grid entries as `χ`-family members (piece 1).
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hPne : P j ≠ P 0 := fun h => hj0 (hPinj h)
  have hPj' : tic.chiFam hVeq app (P j) = hyp.alignedOmegaSigmaGrid hG hodd i j := (hP j).symm
  have hP0' : tic.chiFam hVeq app (P 0) = hyp.alignedOmegaSigmaGrid hG hodd i 0 := (hP 0).symm
  -- `ψ = X − δ·(ω_{ij}^σ − ω_{i0}^σ)` vanishes on `V`.
  have hζvanish : ∀ v ∈ typePV M hyp.typeP, coh.tau1 ζ v = 0 :=
    fun v hv => hyp.tau1_zeta_vanishes_on_typePV hG hodd coh hζS hζirr hζne hv
  have hψV : ∀ v ∈ tic.V,
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.tau1 ζ
        - (δ : ℂ) • (tic.chiFam hVeq app (P j) - tic.chiFam hVeq app (P 0))) v = 0 := by
    intro v hv
    rw [hPj', hP0']
    exact hyp.muGridPsi_vanishes_on_typePV hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj coh hζvanish hv
  -- the norm-`2` Dade-image trichotomy.
  rw [eq_sub_iff_add_eq, ← hPj', ← hP0']
  exact tic.eq_smul_chiFam_diff_of_vanishOnV hVeq app hXZ hXfacts.2 hPne hδpm hψV

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), coherence-free row-difference form**: for nontrivial columns
`j ≠ k` in the same row `i`, `(μ_{ij} − μ_{ik})^τ = δ·(ω_{ij}^σ − ω_{ik}^σ)`.

Unlike `alpha_tau_image` this needs **no** `CoherentHypothesis`: the `n·ζ` legs of the two
`α`'s cancel in the row difference (equal degrees, (10.3) `degree_independent`), so the
`V`-vanishing legs (`tau_muGridAlpha_apply_eq_on_typePV`, coherence-free) subtract to give the
`ψ`-vanishing, and the norm-2 trichotomy engine applies to `X = (μ_{ij} − μ_{ik})^τ` directly.
This is the repo analogue of Coq's coherence-free `FTtypeP_subcoherent` `R`-datum for the
μ-grid (issue 2022, the (5.2.d) reducible-column route). -/
theorem Hypothesis.tau_muGrid_row_diff [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hodd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hodd j = params.delta)
    (i : Fin hyp.w1) {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) (hjk : j ≠ k) :
    hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)
      = (params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i k) := by
  have := hyp.finiteG
  classical
  -- degrees and the `α`-difference identity
  have hdegj : hyp.muGrid hG hodd i j 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i j hj0
  have hdegk : hyp.muGrid hG hodd i k 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i k hk0
  have hμ0 : hyp.muGrid hG hodd i 0 1 = 1 := hyp.muGrid_zero_column_apply_one hG hodd i
  have hα : hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k
      = params.alpha i j - params.alpha i k := by
    rw [params.alpha_def, params.alpha_def, hmu]
    abel
  -- `X ∈ ℤ[Irr G]`: the difference is `A₀`-supported and integral
  have hsupp : (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k).support ⊆ hyp.A0 := by
    rw [hα]
    intro x hx
    rw [ClassFunction.mem_support, ClassFunction.sub_apply] at hx
    by_cases h1 : params.alpha i j x = 0
    · refine params.alpha_support i k hk0 ?_
      rw [ClassFunction.mem_support]
      intro h2
      exact hx (by rw [h1, h2, sub_zero])
    · exact params.alpha_support i j hj0 (ClassFunction.mem_support.mpr h1)
  -- `X ∈ ℤ[Irr G]` via the two `α`-legs
  have hXZ : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k) ∈ ZIrr G := by
    rw [hα, params.alpha_def, params.alpha_def, hmu, map_sub]
    exact Submodule.sub_mem _
      (hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hzS params.zeta_irreducible hdegj hμ0 hz1
        params.n_formula (hδj j hj0))
      (hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hk0 hzS params.zeta_irreducible hdegk hμ0 hz1
        params.n_formula (hδj k hk0))
  -- `‖X‖² = 2`: Dade preserves the inner product on the supported difference
  have hsrc : ClassFunction.inner
      (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)
      (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k) = 2 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right,
      hyp.muGrid_inner_self hG hodd i j, hyp.muGrid_inner_self hG hodd i k,
      hyp.muGrid_inner_cross_column hG hodd i i hjk,
      hyp.muGrid_inner_cross_column hG hodd i i (Ne.symm hjk)]
    ring
  have hX2 : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k))
      (hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)) = 2 := by
    have hset : ∀ s ∈ ({hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k} :
        Set (ClassFunction ↥M ℂ)), s.support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
      rintro s rfl
      exact hsupp
    have hmem : hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k ∈
        OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
          ({hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k} :
            Set (ClassFunction ↥M ℂ)) :=
      Submodule.subset_span rfl
    have hpres := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      hyp.dadeData.dade hset hmem hmem
    rw [show hyp.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData) from rfl]
    rw [hpres]
    exact hsrc
  -- the σ-grid enumeration and the trichotomy engine
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  have hPj' : tic.chiFam hVeq app (P j) = hyp.alignedOmegaSigmaGrid hG hodd i j := (hP j).symm
  have hPk' : tic.chiFam hVeq app (P k) = hyp.alignedOmegaSigmaGrid hG hodd i k := (hP k).symm
  have hPne : P j ≠ P k := fun h => hjk (hPinj h)
  have hψV : ∀ v ∈ tic.V,
      (hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k)
        - (params.delta : ℂ) • (tic.chiFam hVeq app (P j) - tic.chiFam hVeq app (P k))) v
        = 0 := by
    intro v hv
    have hlegj := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj0 hzS hdegj hμ0 hz1
      params.n_formula (hδj j hj0) hv
    have hlegk := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hk0 hzS hdegk hμ0 hz1
      params.n_formula (hδj k hk0) hv
    have hXv : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd i k) v
        = ((params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
            - hyp.alignedOmegaSigmaGrid hG hodd i k)) v := by
      rw [hα, params.alpha_def, params.alpha_def, hmu, map_sub, ClassFunction.sub_apply,
        hlegj, hlegk]
      simp only [ClassFunction.smul_apply, ClassFunction.sub_apply]
      ring
    rw [ClassFunction.sub_apply, hXv, hPj', hPk']
    simp only [ClassFunction.smul_apply, ClassFunction.sub_apply]
    ring
  rw [← hPj', ← hPk']
  exact tic.eq_smul_chiFam_diff_of_vanishOnV hVeq app hXZ hX2 hPne hδpm hψV

open scoped FiniteInduce in
/-- **Column-sum form of `tau_muGrid_row_diff`** (coherence-free (10.5) for columns):
`(μ_j − μ_k)^τ = δ·(∑ω_{ij}^σ − ∑ω_{ik}^σ)` for nontrivial columns `j ≠ k`. -/
theorem Hypothesis.tau_muGrid_columnSum_diff_cohFree [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hodd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hodd j = params.delta)
    {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) (hjk : j ≠ k) :
    hyp.tau (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j
        - ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) =
      (params.delta : ℂ) • (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i j
        - ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd i k) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    hyp.tau_muGrid_row_diff hG hodd hmu hzS hz1 hδpm hδj i hj0 hk0 hjk

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), Dade-image half** (`CharacterParameters` corollary).  For the (10.2)/(10.3)
character data — the `μ`-grid (`hmu`), the aligned `σ`-grid (`hos`), the degree-`w₁` irreducible `ζ`
of (10.2) (`hzS`/`hz1`) and the column sign `δ = ±1` (`hδpm`/`hδj`) — the Dade image of
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` is `δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}`.

Thin corollary of the grid identity `tau_muGridAlpha_eq`.  All arithmetic inputs are discharged from
the (10.3) data carried by `CharacterParameters` (`degree_independent`, `n_formula`, `d_gt_one`,
`two_le_n`) and the structural bounds `w₁, w₂ ≥ 3` (`three_le_card_W1/W2`): the auxiliary nontrivial
column `k ≠ j`, the degree distinctness `d ≠ w₁`/`1 ≠ w₁`, and the parity `n ≥ 2` (Peterfalvi
(10.3),
now `params.two_le_n`).  The only hypotheses beyond the (10.2)/(10.3) construction pins are `hzconj`
— the non-realness `ζ̄ ≠ ζ` (Peterfalvi (1.1): a nontrivial irreducible of an odd-order group is not
real; carried per the §10 (10.5) chain convention, derivable via
`not_isReal_of_ne_trivial_of_odd_card'`). -/
theorem alpha_tau_image [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
        hyp.tau (params.alpha i j) =
          (params.delta : ℂ) • (params.omegaSigma i j - params.omegaSigma i 0)
            - (params.n : ℂ) • coh.tau1 params.zeta := by
  have := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  have hn2 : 2 ≤ params.n := params.two_le_n
  -- structural bounds `w₁, w₂ ≥ 3` from the §10 TI-cyclic hypothesis.
  have hw1 : 3 ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  have hw2 : 3 ≤ hyp.w2 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W2
  intro i j hj0
  -- choose an auxiliary nontrivial column `k ≠ j` (possible as `w₂ ≥ 3`).
  obtain ⟨k, hjk, hk0⟩ : ∃ k : Fin hyp.w2, j ≠ k ∧ k ≠ 0 := by
    have h1lt : 1 < hyp.w2 := by omega
    have h2lt : 2 < hyp.w2 := by omega
    by_cases h : j = ⟨1, h1lt⟩
    · exact ⟨⟨2, h2lt⟩, by rw [h]; exact Fin.ne_of_val_ne (by simp),
        Fin.ne_of_val_ne (by simp)⟩
    · exact ⟨⟨1, h1lt⟩, h, Fin.ne_of_val_ne (by simp)⟩
  -- (10.3) degree facts on the `μ`-grid.
  have hdeg : hyp.muGrid hG hodd i j 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i j hj0
  have hμ0 : hyp.muGrid hG hodd i 0 1 = 1 := hyp.muGrid_zero_column_apply_one hG hodd i
  have hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (params.d : ℂ) := fun i' => by
    rw [← hmu]; exact params.degree_independent i' k hk0
  have hd1 : params.d ≠ 1 := by have := params.d_gt_one; omega
  have hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1 := by rw [hcol1 0]; exact_mod_cast hd1
  -- `d ≠ w₁` from `d = n·w₁ + δ`, `n ≥ 2`, `w₁ ≥ 3`, `δ = ±1`.
  have hdw1 : params.d ≠ hyp.w1 := by
    have hf : (params.d : ℤ) = (params.n : ℤ) * (hyp.w1 : ℤ) + params.delta := by
      linarith [params.n_formula]
    have hn2Z : (2 : ℤ) ≤ (params.n : ℤ) := by exact_mod_cast hn2
    have hw1Z : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw1
    intro he
    have heZ : (params.d : ℤ) = (hyp.w1 : ℤ) := by exact_mod_cast he
    rcases hδpm with h | h <;> rw [h] at hf <;> nlinarith [hf, heZ, hn2Z, hw1Z]
  have hdζ : hyp.muGrid hG hodd i j 1 ≠ params.zeta 1 := by
    rw [hdeg, hz1]; exact_mod_cast hdw1
  have h0ζ : hyp.muGrid hG hodd i 0 1 ≠ params.zeta 1 := by
    rw [hμ0, hz1]; intro he; have : hyp.w1 = 1 := by exact_mod_cast he.symm
    omega
  have hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ params.zeta 1 := fun i' => by
    rw [hcol1 i', hz1]; exact_mod_cast hdw1
  -- discharge via the grid identity `tau_muGridAlpha_eq`.
  rw [params.alpha_def, hmu, hos]
  exact hyp.tau_muGridAlpha_eq hG hodd i hj0 k hjk hk0 coh hzS params.zeta_irreducible hzconj
    hdeg hμ0 hz1 params.n_formula (hδj j hj0) hdζ h0ζ hkζ hcol1 hdk1 hδpm hw1 hn2

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a) reduction**: `(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = δ` for `0 < j < w₂`.

This is the inner-product identity opening the (10.6)(a) proof:
`1 = (α_{ij}, μ_j − dζ̄) = (α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = (δ(ω_{ij}^σ − ω_{i0}^σ), μ_j^{τ₁})`.
From the diagonal reduction `(α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = 1`
(`muGridAlpha_tau1_inner_muColumn_self_sub_conj`), the vanishing `(α_{ij}^τ, ζ̄^{τ₁}) = 0`
(from `(α_{ij}^τ, ζ^{τ₁}) = −n` (`muGridAlpha_tau1_zeta_eq_neg_n`, the (10.5) `a = 0`) and
`(α_{ij}^τ, ζ̄^{τ₁}) = (α_{ij}^τ, ζ^{τ₁}) + n` (`muGridAlpha_tau_inner_zeta_sub_conj`)), the (10.5)
Dade image `α_{ij}^τ = δ(ω_{ij}^σ − ω_{i0}^σ) − nζ^{τ₁}` (`alpha_tau_image`) and
`(ζ^{τ₁}, μ_j^{τ₁}) = 0`
(`zeta_tau1_inner_muColumn`): `1 = (α_{ij}^τ, μ_j^{τ₁}) = δ(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁})`, hence
`(ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = δ` (`δ² = 1`).  This pins the `j`-column coefficient of
`μ_j^{τ₁}` along `ω_{ij}^σ` to `δ` for every `i`, which together with `‖μ_j^{τ₁}‖² = w₁` forces the
(10.6)(a) summed isometry `μ_j^{τ₁} = δ∑_i ω_{ij}^σ` (see `muColumn_tau1_pin`).  Crucially this
specialised reduction avoids Peterfalvi's general (5.8) machinery (separability / `σ`-coefficients):
the diagonal inner product `= 1` directly determines the `j`-column. -/
theorem Hypothesis.omegaSigmaDiff_inner_muColumn_tau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} {hyp : Hypothesis M}
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j : Fin hyp.w2} (hj0 : j ≠ 0) (i : Fin hyp.w1) :
    ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' j)) = (params.delta : ℂ) := by
  have := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  -- discharge the standard (10.3) degree/parity hypotheses (cf. `alpha_tau_image`).
  have hn2 : 2 ≤ params.n := params.two_le_n
  have hw1 : 3 ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  have hw2 : 3 ≤ hyp.w2 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W2
  obtain ⟨k, hjk, hk0⟩ : ∃ k : Fin hyp.w2, j ≠ k ∧ k ≠ 0 := by
    have h1lt : 1 < hyp.w2 := by omega
    have h2lt : 2 < hyp.w2 := by omega
    by_cases h : j = ⟨1, h1lt⟩
    · exact ⟨⟨2, h2lt⟩, by rw [h]; exact Fin.ne_of_val_ne (by simp), Fin.ne_of_val_ne (by simp)⟩
    · exact ⟨⟨1, h1lt⟩, h, Fin.ne_of_val_ne (by simp)⟩
  have hdeg : hyp.muGrid hG hodd i j 1 = (params.d : ℂ) := by
    rw [← hmu]; exact params.degree_independent i j hj0
  have hμ0 : hyp.muGrid hG hodd i 0 1 = 1 := hyp.muGrid_zero_column_apply_one hG hodd i
  have hcolj : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 = (params.d : ℂ) := fun i' => by
    rw [← hmu]; exact params.degree_independent i' j hj0
  have hcolk : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (params.d : ℂ) := fun i' => by
    rw [← hmu]; exact params.degree_independent i' k hk0
  have hd1 : params.d ≠ 1 := by have := params.d_gt_one; omega
  have hdj1 : hyp.muGrid hG hodd 0 j 1 ≠ 1 := by rw [hcolj 0]; exact_mod_cast hd1
  have hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1 := by rw [hcolk 0]; exact_mod_cast hd1
  have hdw1 : params.d ≠ hyp.w1 := by
    have hf : (params.d : ℤ) = (params.n : ℤ) * (hyp.w1 : ℤ) + params.delta := by
      linarith [params.n_formula]
    have hn2Z : (2 : ℤ) ≤ (params.n : ℤ) := by exact_mod_cast hn2
    have hw1Z : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw1
    intro he
    have heZ : (params.d : ℤ) = (hyp.w1 : ℤ) := by exact_mod_cast he
    rcases hδpm with h | h <;> rw [h] at hf <;> nlinarith [hf, heZ, hn2Z, hw1Z]
  have hdζ : hyp.muGrid hG hodd i j 1 ≠ params.zeta 1 := by rw [hdeg, hz1]; exact_mod_cast hdw1
  have h0ζ : hyp.muGrid hG hodd i 0 1 ≠ params.zeta 1 := by
    rw [hμ0, hz1]; intro he; have : hyp.w1 = 1 := by exact_mod_cast he.symm
    omega
  have hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ params.zeta 1 := fun i' => by
    rw [hcolj i', hz1]; exact_mod_cast hdw1
  have hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ params.zeta 1 := fun i' => by
    rw [hcolk i', hz1]; exact_mod_cast hdw1
  have hζirr := params.zeta_irreducible
  have hδjj := hδj j hj0
  -- (1) the diagonal reduction `(α^τ, μ_j^{τ₁} − dζ̄^{τ₁}) = 1`.
  have hdiag := hyp.muGridAlpha_tau1_inner_muColumn_self_sub_conj hG hodd i hj0 coh hzS hζirr
    hzconj hdeg hμ0 hz1 params.n_formula hδjj h0ζ hjζ hcolj hdj1
  -- (2) `(α^τ, ζ^{τ₁}) = −n` (the (10.5) `a = 0`).
  have haζ := hyp.muGridAlpha_tau1_zeta_eq_neg_n hG hodd i hj0 k hjk hk0 coh hzS hζirr hzconj
    hdeg hμ0 hz1 params.n_formula hδjj hdζ h0ζ hkζ hcolk hdk1 hδpm hw1 hn2
  -- (3) `(α^τ, ζ^{τ₁}) − (α^τ, ζ̄^{τ₁}) = −n`, hence `(α^τ, ζ̄^{τ₁}) = 0`.
  have hzsc := hyp.muGridAlpha_tau_inner_zeta_sub_conj hG hodd i hj0 hzS hζirr hzconj
    hdeg hμ0 hz1 params.n_formula hδjj hdζ h0ζ
  rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hzS hζirr, ClassFunction.inner_sub_right] at hzsc
  have haζbar : ClassFunction.inner
      (hyp.tau (hyp.muGrid hG hodd i j - (params.delta : ℂ) • hyp.muGrid hG hodd i 0
        - (params.n : ℂ) • params.zeta)) (coh.tau1 params.zeta.conj) = 0 := by
    linear_combination haζ - hzsc
  -- (4) `(α^τ, μ_j^{τ₁}) = 1`.
  rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right, haζbar,
    mul_zero, sub_zero] at hdiag
  -- (5) substitute the (10.5) Dade image and drop the `ζ^{τ₁}` term (`(ζ^{τ₁}, μ_j^{τ₁}) = 0`).
  have hαimg := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i j hj0
  rw [params.alpha_def, hmu, hos] at hαimg
  have hζμ := hyp.zeta_tau1_inner_muColumn hG hodd j coh hzS hζirr hjζ hdj1
  rw [hαimg, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    ClassFunction.inner_smul_left, hζμ, mul_zero, sub_zero] at hdiag
  -- `δ · (ω_{ij}^σ − ω_{i0}^σ, μ_j^{τ₁}) = 1`, so the inner product is `δ` (`δ² = 1`).
  have hδsq : (params.delta : ℂ) * (params.delta : ℂ) = 1 := by
    rcases hδpm with h | h <;> rw [h] <;> norm_num
  calc ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j
          - hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' j))
      = (params.delta : ℂ) * ((params.delta : ℂ) * ClassFunction.inner
          (hyp.alignedOmegaSigmaGrid hG hG.odd i j - hyp.alignedOmegaSigmaGrid hG hG.odd i 0)
          (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' j))) := by
        rw [← mul_assoc, hδsq, one_mul]
    _ = (params.delta : ℂ) * 1 := by rw [hdiag]
    _ = (params.delta : ℂ) := mul_one _

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), column difference (per row)**: for two nontrivial columns `j, k ≠ 0`, the
Dade image of the difference `μ_{ij} − μ_{ik}` of certain-type characters is
`δ·(ω_{ij}^σ − ω_{ik}^σ)`.

The `−δ·μ_{i0} − n·ζ` tails of `α_{ij}` and `α_{ik}` are identical, so `μ_{ij} − μ_{ik} =
α_{ij} − α_{ik}`, and applying `alpha_tau_image` to both columns the `−n·ζ^{τ₁}` parts cancel.  This
is the per-row ingredient of the column image-family `image_eq` (the §10 analogue of the Peterfalvi
(4.9) summed Dade identity), feeding the (5.5)-for-columns route to (10.6)(a). -/
theorem tau_muGrid_column_diff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (i : Fin hyp.w1) {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) :
    hyp.tau (hyp.muGrid hG hG.odd i j - hyp.muGrid hG hG.odd i k) =
      (params.delta : ℂ) • (hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - hyp.alignedOmegaSigmaGrid hG hG.odd i k) := by
  have hatj := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i j hj0
  have hatk := alpha_tau_image hG coh hmu hos hzS hz1 hzconj hδpm hδj i k hk0
  have halpha : hyp.muGrid hG hG.odd i j - hyp.muGrid hG hG.odd i k
      = params.alpha i j - params.alpha i k := by
    rw [params.alpha_def, params.alpha_def, hmu]; abel
  rw [halpha, map_sub, hatj, hatk, hos]
  simp only [smul_sub]; abel

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), column-sum difference**: summing `tau_muGrid_column_diff` over the rows
`0 ≤ i < w₁`, the Dade image of the difference of the two column characters `μ_j = ∑_i μ_{ij}` and
`μ_k = ∑_i μ_{ik}` (`j, k ≠ 0`) is `δ·(∑_i ω_{ij}^σ − ∑_i ω_{ik}^σ)`.

This is the §10 analogue of the Peterfalvi (4.9) summed Dade identity: it computes
`(μ_j − μ_k)^τ = ∑_{α ∈ R} α` over the signed `σ`-image family
`R = {δ·ω_{ij}^σ} ∪ {−δ·ω_{ik}^σ}`, the `image_eq` field of the column image family used by the
(5.5)-for-columns route to (10.6)(a). -/
theorem tau_muGrid_columnSum_diff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    {j k : Fin hyp.w2} (hj0 : j ≠ 0) (hk0 : k ≠ 0) :
    hyp.tau (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j
        - ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) =
      (params.delta : ℂ) • (∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i j
        - ∑ i : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i k) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    tau_muGrid_column_diff hG coh hmu hos hzS hz1 hzconj hδpm hδj i hj0 hk0

open scoped FiniteInduce in
/-- **§10 conjugate column** (Peterfalvi (4.9)(a) at §10): for a nontrivial column `j ≠ 0`, the
complex conjugate of the column character `μ_j = ∑_i μ_{ij}` is another nontrivial column
`μ_{j'} = ∑_i μ_{ij'}` with `j' ≠ 0` and `j' ≠ j` (`j'` is the column of `χ₂⁻¹`).

Reduces to the §6 `certainType_columnSum_conj` (`μ̄_j = ∑_i μ_{i,χ₂⁻¹}`), which (issue 1010, HUB) is
now stated on the structural `Hypothesis ↥M`, hence applies to the §10 muGrid host
`(hyp.toCertainTypeHypothesis hG hodd).toHypothesis`.  The `muGrid ↔ columnFamily` row reindexing
gives `∑_i μ_{ij} = ∑_{i'} (h.columnFamily (χ₂ j)).mu i'`; complex conjugation (`ClassFunction.conj`
= `mapRingEquiv conj` pointwise) sends it to the `χ₂⁻¹`-column.  `j' ≠ 0` from
`finCardEquivCharacterGroup_zero` (the column-`0` dual is trivial) and `j' ≠ j` from the odd order
of
the column character group (`W_odd`/`card_charGroup_W2`, no involutions; the `column_inv_ne_self`
argument inlined).  This is the conjugate-column input `(μ_j)‾ = μ_{j'}` for the (5.5)-for-columns
route to (10.6)(a): `tau_muGrid_columnSum_diff` (with `k = j'`) then supplies the column
`OrthonormalCharacterImageFamily.image_eq` field `τ(μ_j − μ̄_j) = ∑ R(μ_j)`. -/
theorem Hypothesis.exists_conj_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    ∃ j' : Fin hyp.w2, j' ≠ 0 ∧ j' ≠ j ∧
      (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j).conj
        = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j' := by
  have := hyp.finiteG
  have : Finite ↥M := inferInstance
  classical
  -- reconstruct the §6 structural host (as in `muGrid`)
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- the column character as a function of the index
  let χ₂ : Fin hyp.w2 → ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    fun jj => finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm jj)
  -- the `muGrid ↔ columnFamily` row-reindexing bridge
  have hbridge : ∀ jj : Fin hyp.w2,
      ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i jj
        = ∑ i' : Fin (Nat.card h.W1), ((h.columnFamily (χ₂ jj)).mu i' : ClassFunction ↥M ℂ) := by
    intro jj
    rw [← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily (χ₂ jj)).mu i' : ClassFunction ↥M ℂ))]
    exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
  -- `ClassFunction.conj = mapRingEquiv conj` pointwise
  have hconjbridge : ∀ X : ClassFunction ↥M ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  -- `χ₂` injective; `χ₂ jj = 1 ↔ jj = 0`
  have hχ₂inj : Function.Injective χ₂ := fun a b hab =>
    (finCongr hcardW2sub.symm).injective ((finCardEquivCharacterGroup _).injective hab)
  have hχ₂one : ∀ jj : Fin hyp.w2, χ₂ jj = 1 ↔ jj = 0 := by
    intro jj
    rw [show (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
        = finCardEquivCharacterGroup _ 0 from (finCardEquivCharacterGroup_zero _).symm,
      (finCardEquivCharacterGroup _).injective.eq_iff]
    constructor
    · intro he; exact (finCongr hcardW2sub.symm).injective (by rw [he]; simp)
    · intro he; subst he; simp
  -- the conjugate-column index `j'` with `χ₂ j' = (χ₂ j)⁻¹`
  let j' : Fin hyp.w2 :=
    (finCongr hcardW2sub.symm).symm ((finCardEquivCharacterGroup _).symm (χ₂ j)⁻¹)
  have hj'χ : χ₂ j' = (χ₂ j)⁻¹ := by simp only [χ₂, j', Equiv.apply_symm_apply]
  have hχ₂jne : χ₂ j ≠ 1 := fun he => hj0 ((hχ₂one j).mp he)
  -- `(χ₂ j)⁻¹ ≠ χ₂ j` (column char group has odd order — no involutions; `column_inv_ne_self`
  -- inline)
  have hinvne : (χ₂ j)⁻¹ ≠ χ₂ j := by
    have hodd' : Odd (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) := by
      rw [h.card_charGroup_W2]
      exact h.W_odd.of_dvd_nat (Subgroup.card_dvd_of_le le_sup_right)
    intro heq
    apply hχ₂jne
    have hsq : (χ₂ j) ^ 2 = 1 := by
      have hm := mul_inv_cancel (χ₂ j); rw [heq] at hm; rwa [pow_two]
    have hcardodd : Odd (orderOf (χ₂ j)) := hodd'.of_dvd_nat (orderOf_dvd_natCard (χ₂ j))
    have h1 : orderOf (χ₂ j) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h2 | h2
      · exact h2
      · exact absurd (h2 ▸ hcardodd) (by decide)
    exact orderOf_eq_one_iff.mp h1
  refine ⟨j', ?_, ?_, ?_⟩
  · -- `j' ≠ 0`
    intro he
    apply hχ₂jne
    have hjinvone : (χ₂ j)⁻¹ =
        (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
      hj'χ ▸ (hχ₂one j').mpr he
    have hinv := congrArg
      (fun z : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ => z⁻¹) hjinvone
    have hinvinv : ((χ₂ j)⁻¹)⁻¹ = χ₂ j :=
      @inv_inv ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _ (χ₂ j)
    have hinvone : ((1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)⁻¹) = 1 :=
      @inv_one ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _
    simpa only [hinvinv, hinvone] using hinv
  · -- `j' ≠ j`
    intro he
    exact hinvne (hj'χ ▸ (congrArg χ₂ he))
  · -- the conjugate identity, via the generalized §6 `certainType_columnSum_conj`
    rw [hbridge j, hbridge j', hconjbridge,
      OddOrder.Peterfalvi.S06.certainType_columnSum_conj h (χ₂ j), hj'χ]

/-- **§10 `R(μ_j)` member family** (Peterfalvi (5.3.b) at §10).  Indexed by `Bool × Fin w₁`:
`(false, i) ↦ δ·ω_{ij}^σ`, `(true, i) ↦ −δ·ω_{ij'}^σ` (sign `δ = params.delta`, columns `j`, `j'`).
Its image is the orthonormal difference-image family `R(μ_j)` of the column
`OrthonormalCharacterImageFamily`. -/
noncomputable def Hypothesis.columnRImage [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (δ : ℤ) (j j' : Fin hyp.w2) :
    Bool × Fin hyp.w1 → ClassFunction G ℂ
  | (false, i) => (δ : ℂ) • hyp.alignedOmegaSigmaGrid hG hodd i j
  | (true, i) => (-(δ : ℂ)) • hyp.alignedOmegaSigmaGrid hG hodd i j'

end OddOrder.Peterfalvi.S12


