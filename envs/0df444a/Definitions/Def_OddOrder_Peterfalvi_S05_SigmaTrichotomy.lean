-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S05_SigmaTrichotomy
-- name    : OddOrder_Peterfalvi_S05_SigmaTrichotomy
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:00:50.421264+00:00
-- url     : https://prove2.me/theorems/231c7ea8-5e46-4d9f-ad07-d1a669e59f7e
-- title:
--   Peterfalvi (3.8): the trichotomy for the $\sigma$-coefficient grid
-- statement:
--   Formalizes Peterfalvi (3.8) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §3, pp. 15-20): it specializes the abstract grid trichotomy to the concrete $\sigma$-image coefficient grid.
--
--   Main declarations: `sigmaCoeff_eq_zero_of_vanishOnV` (All σ-coefficients of a norm-`2` `V`-vanishing virtual character vanish); `sigmaCoeff_sub_smul_chiFam_diff` (The σ-coefficient grid of ψ = X − s·(χ_{P₁} − χ_{P₂}) (s); `eq_sum_sigmaCoeff_smul_chiFam_of_inner_self_eq` (Fourier reconstruction along the orthonormal `σ`-image family); `eq_smul_chiFam_column_of_vanishOnV` (Peterfalvi (5.8), `σ`-coefficient full-column endgame).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S05_SigmaTrichotomy.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_SigmaTrichotomy.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_SigmaIsometry
import Definitions.Def_OddOrder_Peterfalvi_S05_GridTrichotomy

namespace OddOrder.Peterfalvi.S05.TICyclicHypothesis

open OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

/-- **Peterfalvi Theorem (3.8)** (full trichotomy for the `σ`-coefficient grid).  Let `ψ` vanish on
`V`, with `w₁ + 2 ≤ w₂` (the odd-order gap from `w₁ < w₂`) and `NC(ψ) < 2w₁`.  Then one of:

* (a) every `σ`-image coefficient `⟨ψ, ω_{ij}^σ⟩` vanishes (`ψ = β`, orthogonal to `Im σ`);
* (b) a single `W₂`-column `j₀` carries a common nonzero coefficient `c`, the rest vanishing
  (`ψ = c·∑_i ω_{i,j₀}^σ + β`);
* (c) a single `W₁`-row `i₀` carries a common nonzero coefficient `c`, the rest vanishing
  (`ψ = c·∑_j ω_{i₀,j}^σ + β`).

Immediate from `grid_trichotomy` applied to `sigmaCoeff`, whose additive separability is
`sigmaCoeff_add_eq` (3.7) and whose support count is `sigmaNC` (3.6) by definition; the index sets
`Ŵ₁, Ŵ₂` have `|Ŵ_k| = w_k` (`card_charGroup_subgroupOf`). -/
theorem sigmaCoeff_trichotomy (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {ψ : ClassFunction G ℂ} (hψ : ∀ v ∈ hyp.V, ψ v = 0)
    (hgap : Nat.card hyp.W1 + 2 ≤ Nat.card hyp.W2)
    (hNC : hyp.sigmaNC hVeq app ψ < 2 * Nat.card hyp.W1) :
    (∀ pq, hyp.sigmaCoeff hVeq app ψ pq = 0) ∨
      (∃ (j₀ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) (c : ℂ), c ≠ 0 ∧
        (∀ p, hyp.sigmaCoeff hVeq app ψ (p, j₀) = c) ∧
        ∀ p q, q ≠ j₀ → hyp.sigmaCoeff hVeq app ψ (p, q) = 0) ∨
      (∃ (i₀ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (c : ℂ), c ≠ 0 ∧
        (∀ q, hyp.sigmaCoeff hVeq app ψ (i₀, q) = c) ∧
        ∀ p q, p ≠ i₀ → hyp.sigmaCoeff hVeq app ψ (p, q) = 0) := by
  have : Finite G := Finite.of_fintype G
  have : Nonempty ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  have : Nonempty ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  refine grid_trichotomy (fun pq => hyp.sigmaCoeff hVeq app ψ pq)
    (fun p p' q q' => hyp.sigmaCoeff_add_eq hVeq app hψ p p' q q') ?_ ?_
  · rw [hyp.card_charGroup_subgroupOf hyp.W1_le_W, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
    exact hgap
  · rw [hyp.card_charGroup_subgroupOf hyp.W1_le_W]
    exact hNC

open scoped Classical in
/-- **All σ-coefficients of a norm-`2` `V`-vanishing virtual character vanish** — the
degenerate all-zero case of the (4.8)/(10.5) trichotomy.  `ŵ₁, ŵ₂ ≥ 3`, both odd and
coprime, so a `+2`-gap holds in one orientation; `NC(X) ≤ 2 < 3 ≤ min(ŵ₁, ŵ₂)` kills the
constant-row/column branches of `grid_trichotomy`. -/
theorem sigmaCoeff_eq_zero_of_vanishOnV (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {X : ClassFunction G ℂ} (hXZ : X ∈ ZIrr G) (hX2 : ClassFunction.inner X X = 2)
    (hXV : ∀ v ∈ hyp.V, X v = 0) :
    ∀ pq, hyp.sigmaCoeff hVeq app X pq = 0 := by
  have : Finite G := Finite.of_fintype G
  have : Nonempty ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  have : Nonempty ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  have : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  set a : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) → ℂ :=
    fun pq => hyp.sigmaCoeff hVeq app X pq with ha
  have hadd : ∀ p p' q q', a (p, q) + a (p', q') = a (p, q') + a (p', q) :=
    fun p p' q q' => hyp.sigmaCoeff_add_eq hVeq app hXV p p' q q'
  have hNC : {x | a x ≠ 0}.ncard ≤ 2 :=
    hyp.ncard_sigmaCoeff_ne_zero_le_two hVeq app hXZ hX2
  have hcard1 : Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) = Nat.card hyp.W1 :=
    hyp.card_charGroup_subgroupOf hyp.W1_le_W
  have hcard2 : Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) = Nat.card hyp.W2 :=
    hyp.card_charGroup_subgroupOf hyp.W2_le_W
  have h31 := hyp.three_le_card_W1
  have h32 := hyp.three_le_card_W2
  have hodd1 : Odd (Nat.card hyp.W1) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
  have hodd2 : Odd (Nat.card hyp.W2) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
  have hcop := hyp.W_card_coprime
  have hwne : Nat.card hyp.W1 ≠ Nat.card hyp.W2 := by
    intro he
    rw [he, Nat.Coprime, Nat.gcd_self] at hcop
    omega
  -- branch killers: a constant nonzero row/column of length `≥ 3` contradicts `NC ≤ 2`
  have hkill1 : ∀ (j₀ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) (c : ℂ), c ≠ 0 →
      (∀ p, a (p, j₀) = c) → False := by
    intro j₀ c hc0 hcol
    have hsub : (Set.image (fun p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ => (p, j₀))
        Set.univ) ⊆ {x | a x ≠ 0} := by
      rintro _ ⟨p, -, rfl⟩
      rw [Set.mem_ofPred_eq, hcol p]
      exact hc0
    have hge : 3 ≤ {x | a x ≠ 0}.ncard := by
      have himg : (Set.image (fun p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ => (p, j₀))
          Set.univ).ncard
          = Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := by
        rw [Set.ncard_image_of_injective _
          (fun x y h => (Prod.mk.injEq _ _ _ _).mp h |>.1), Set.ncard_univ]
      calc 3 ≤ Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := by rw [hcard1]; omega
        _ = _ := himg.symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hkill2 : ∀ (i₀ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (c : ℂ), c ≠ 0 →
      (∀ q, a (i₀, q) = c) → False := by
    intro i₀ c hc0 hrow
    have hsub : (Set.image (fun q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ => (i₀, q))
        Set.univ) ⊆ {x | a x ≠ 0} := by
      rintro _ ⟨q, -, rfl⟩
      rw [Set.mem_ofPred_eq, hrow q]
      exact hc0
    have hge : 3 ≤ {x | a x ≠ 0}.ncard := by
      have himg : (Set.image (fun q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ => (i₀, q))
          Set.univ).ncard
          = Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := by
        rw [Set.ncard_image_of_injective _
          (fun x y h => (Prod.mk.injEq _ _ _ _).mp h |>.2), Set.ncard_univ]
      calc 3 ≤ Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := by rw [hcard2]; omega
        _ = _ := himg.symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  intro pq
  by_contra hne0
  rcases lt_or_gt_of_ne hwne with hlt | hgt
  · -- `ŵ₁ < ŵ₂`: gap in the standard orientation
    have hgap : Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) + 2
        ≤ Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := by
      rw [hcard1, hcard2]
      rcases hodd1 with ⟨m, hm⟩
      rcases hodd2 with ⟨n, hn⟩
      omega
    have hlt2 : {x | a x ≠ 0}.ncard
        < 2 * Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := by
      rw [hcard1]
      omega
    rcases grid_trichotomy a hadd hgap hlt2 with hz | ⟨j₀, c, hc0, hcol, -⟩
      | ⟨i₀, c, hc0, hrow, -⟩
    · exact hne0 (hz pq)
    · exact hkill1 j₀ c hc0 hcol
    · exact hkill2 i₀ c hc0 hrow
  · -- `ŵ₂ < ŵ₁`: transpose the grid
    set a' : ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) → ℂ :=
      fun qp => a (qp.2, qp.1) with ha'
    have hadd' : ∀ q q' p p', a' (q, p) + a' (q', p') = a' (q, p') + a' (q', p) :=
      fun q q' p p' => (hadd p p' q q').trans (add_comm _ _)
    have hsetE : {x | a' x ≠ 0} = Prod.swap '' {x | a x ≠ 0} := by
      ext y
      constructor
      · intro hy
        exact ⟨(y.2, y.1), hy, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz
    have hNC' : {x | a' x ≠ 0}.ncard ≤ 2 := by
      rw [hsetE, Set.ncard_image_of_injective _ Prod.swap_injective]
      exact hNC
    have hgap' : Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) + 2
        ≤ Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := by
      rw [hcard1, hcard2]
      rcases hodd1 with ⟨m, hm⟩
      rcases hodd2 with ⟨n, hn⟩
      omega
    have hlt2' : {x | a' x ≠ 0}.ncard
        < 2 * Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := by
      rw [hcard2]
      omega
    rcases grid_trichotomy a' hadd' hgap' hlt2' with hz | ⟨p₀, c, hc0, hcol, -⟩
      | ⟨q₀, c, hc0, hrow, -⟩
    · exact hne0 (hz (pq.2, pq.1))
    · exact hkill2 p₀ c hc0 (fun q => hcol q)
    · exact hkill1 q₀ c hc0 (fun p => hrow p)

open scoped Classical in
/-- The `σ`-coefficient grid of `ψ = X − s·(χ_{P₁} − χ_{P₂})` (`s : ℤ`).  As the `χ`-family is
orthonormal (`chiFam_spec`), the `s`-part contributes `∓s` exactly at the two grid positions
`P₁, P₂`: `⟨ψ, χ_{pq}⟩ = ⟨X, χ_{pq}⟩ − s·([P₁ = pq] − [P₂ = pq])`.  The `TICyclicHypothesis`-level
generalisation of the §6 `sigmaCoeff_psi_eq`, used by the (4.8)/(10.5) Dade-image trichotomy. -/
theorem sigmaCoeff_sub_smul_chiFam_diff (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (X : ClassFunction G ℂ) (s : ℤ)
    (P1 P2 pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.sigmaCoeff hVeq app
        (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) pq
      = hyp.sigmaCoeff hVeq app X pq
        - (s : ℂ) * ((if P1 = pq then (1 : ℂ) else 0) - (if P2 = pq then (1 : ℂ) else 0)) := by
  simp only [sigmaCoeff, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    (hyp.chiFam_spec hVeq app).2.2.1]

/-- **Norm-`2` Dade image is `s·(χ_{P₁} − χ_{P₂})` once all `σ`-coefficients of the difference
vanish.**  If every `σ`-image coefficient of `ψ = X − s·(χ_{P₁} − χ_{P₂})` vanishes (with
`‖X‖² = 2`, `P₁ ≠ P₂`, `s = ±1`), then `X = s·(χ_{P₁} − χ_{P₂})`.

`⟨ψ, χ_{P₁}⟩ = ⟨ψ, χ_{P₂}⟩ = 0` (hypothesis) and `sigmaCoeff_sub_smul_chiFam_diff` pin
`⟨X, χ_{P₁}⟩ = s`, `⟨X, χ_{P₂}⟩ = −s`; then `‖ψ‖² = ‖X‖² − 2 = 0` (orthonormality of the `χ`-family,
`s² = 1`), so `ψ = 0`.  Generalises the §6 `certainType_diff_dade_eq_of_all_sigmaCoeff_zero`. -/
theorem eq_smul_chiFam_diff_of_all_sigmaCoeff_zero (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {X : ClassFunction G ℂ} (hX2 : ClassFunction.inner X X = 2)
    {P1 P2 : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)}
    (hPne : P1 ≠ P2) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hall : ∀ pq, hyp.sigmaCoeff hVeq app
        (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) pq = 0) :
    X = (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2) := by
  classical
  have hc1 : ClassFunction.inner X (hyp.chiFam hVeq app P1) = (s : ℂ) := by
    have he := hall P1
    rw [hyp.sigmaCoeff_sub_smul_chiFam_diff hVeq app X s P1 P2 P1, if_pos rfl,
      if_neg (Ne.symm hPne)] at he
    change hyp.sigmaCoeff hVeq app X P1 = _
    linear_combination he
  have hc2 : ClassFunction.inner X (hyp.chiFam hVeq app P2) = -(s : ℂ) := by
    have he := hall P2
    rw [hyp.sigmaCoeff_sub_smul_chiFam_diff hVeq app X s P1 P2 P2, if_neg hPne, if_pos rfl] at he
    change hyp.sigmaCoeff hVeq app X P2 = _
    linear_combination he
  have h11 : ClassFunction.inner (hyp.chiFam hVeq app P1) (hyp.chiFam hVeq app P1) = 1 := by
    rw [(hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  have h22 : ClassFunction.inner (hyp.chiFam hVeq app P2) (hyp.chiFam hVeq app P2) = 1 := by
    rw [(hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  have h12 : ClassFunction.inner (hyp.chiFam hVeq app P1) (hyp.chiFam hVeq app P2) = 0 := by
    rw [(hyp.chiFam_spec hVeq app).2.2.1, if_neg hPne]
  have h21 : ClassFunction.inner (hyp.chiFam hVeq app P2) (hyp.chiFam hVeq app P1) = 0 := by
    rw [(hyp.chiFam_spec hVeq app).2.2.1, if_neg (Ne.symm hPne)]
  have hc1' : ClassFunction.inner (hyp.chiFam hVeq app P1) X = (s : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hc1, star_intCast]
  have hc2' : ClassFunction.inner (hyp.chiFam hVeq app P2) X = -(s : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hc2, star_neg, star_intCast]
  have hsq : (s : ℂ) * (s : ℂ) = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hself : ClassFunction.inner
      (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2))
      (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) = 0 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hX2, hc1,
      hc2, hc1', hc2', h11, h22, h12, h21, star_intCast]
    linear_combination (-2 : ℂ) * hsq
  have hfin := eq_zero_of_inner_self_re_eq_zero (G := G)
    (φ := X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) (by rw [hself]; simp)
  rwa [sub_eq_zero] at hfin

/-- **Norm-`2` Dade-image trichotomy endgame** (Peterfalvi (4.8) conclusion (3) / (10.5)).  A
virtual
character `X ∈ ℤ[Irr G]` with `‖X‖² = 2` whose difference `ψ = X − s·(χ_{P₁} − χ_{P₂})` (`s = ±1`,
`P₁ ≠ P₂`) vanishes on `V` satisfies `X = s·(χ_{P₁} − χ_{P₂})`.

`ψ`'s `σ`-coefficient grid is additively separable (3.7) with `NC(ψ) ≤ 4` (the `NC(X) ≤ 2` of the
norm-`2` `X` plus the two indices `P₁, P₂`).  As `w₁, w₂` are coprime odd (`≥ 3`), one of
`w₁ + 2 ≤ w₂`, `w₂ + 2 ≤ w₁` holds, so `NC(ψ) < 2·min(w₁,w₂)` and the (3.8) trichotomy
`grid_trichotomy` applies; the constant-column/row branches are impossible
(`grid_no_constant_column` on the grid resp. transpose, using `NC(X) ≤ 2` and `σ`-coefficients in
`{0,±1}`), so all coefficients vanish and `eq_smul_chiFam_diff_of_all_sigmaCoeff_zero` finishes.
Generalises the §6 `certainType_diff_dade_eq`. -/
theorem eq_smul_chiFam_diff_of_vanishOnV (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {X : ClassFunction G ℂ} (hXZ : X ∈ ZIrr G) (hX2 : ClassFunction.inner X X = 2)
    {P1 P2 : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)}
    (hPne : P1 ≠ P2) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hψV : ∀ v ∈ hyp.V,
        (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) v = 0) :
    X = (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2) := by
  classical
  have : Finite G := Finite.of_fintype G
  have : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Nonempty ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  have : Nonempty ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := ⟨1⟩
  apply hyp.eq_smul_chiFam_diff_of_all_sigmaCoeff_zero hVeq app hX2 hPne hs
  set a : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) → ℂ :=
    fun pq => hyp.sigmaCoeff hVeq app
      (X - (s : ℂ) • (hyp.chiFam hVeq app P1 - hyp.chiFam hVeq app P2)) pq with ha
  set Gr : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) → ℂ :=
    fun pq => hyp.sigmaCoeff hVeq app X pq with hGr
  have hae : ∀ pq, a pq = Gr pq - (s : ℂ) *
      ((if P1 = pq then (1 : ℂ) else 0) - (if P2 = pq then (1 : ℂ) else 0)) :=
    fun pq => hyp.sigmaCoeff_sub_smul_chiFam_diff hVeq app X s P1 P2 pq
  have hG2 : {x | Gr x ≠ 0}.ncard ≤ 2 := hyp.ncard_sigmaCoeff_ne_zero_le_two hVeq app hXZ hX2
  have hG01 : ∀ x, Gr x = 0 ∨ Gr x = 1 ∨ Gr x = -1 :=
    fun x => hyp.sigmaCoeff_eq_zero_or_one_of_inner_self_two hVeq app hXZ hX2 x
  have hsc : (s : ℂ) = 1 ∨ (s : ℂ) = -1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hadd : ∀ p p' q q', a (p, q) + a (p', q') = a (p, q') + a (p', q) :=
    fun p p' q q' => hyp.sigmaCoeff_add_eq hVeq app hψV p p' q q'
  have hNC4 : {x | a x ≠ 0}.ncard ≤ 4 := by
    have hsub : {x | a x ≠ 0} ⊆ {x | Gr x ≠ 0} ∪ {P1, P2} := by
      intro x hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or, not_not] at hcon
      exact hx (by rw [hae x, hcon.1, if_neg (Ne.symm hcon.2.1), if_neg (Ne.symm hcon.2.2)]; ring)
    have hbpair : ({P1, P2} : Set _).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    calc {x | a x ≠ 0}.ncard ≤ ({x | Gr x ≠ 0} ∪ {P1, P2}).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_univ.subset (Set.subset_univ _))
      _ ≤ {x | Gr x ≠ 0}.ncard + ({P1, P2} : Set _).ncard := Set.ncard_union_le _ _
      _ ≤ 2 + 2 := add_le_add hG2 hbpair
      _ = 4 := rfl
  have h3w1 : 3 ≤ Nat.card hyp.W1 := hyp.three_le_card_W1
  have h3w2 : 3 ≤ Nat.card hyp.W2 := hyp.three_le_card_W2
  have hcard1 : Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) = Nat.card hyp.W1 :=
    hyp.card_charGroup_subgroupOf hyp.W1_le_W
  have hcard2 : Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) = Nat.card hyp.W2 :=
    hyp.card_charGroup_subgroupOf hyp.W2_le_W
  have hodd1 : Odd (Nat.card hyp.W1) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
  have hodd2 : Odd (Nat.card hyp.W2) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
  have hcop : Nat.Coprime (Nat.card hyp.W1) (Nat.card hyp.W2) := hyp.W_card_coprime
  have hwne : Nat.card hyp.W1 ≠ Nat.card hyp.W2 := by
    intro he; rw [he, Nat.Coprime, Nat.gcd_self] at hcop; omega
  rcases lt_or_gt_of_ne hwne with hlt | hgt
  · have hgap : Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) + 2
        ≤ Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := by
      rw [hcard1, hcard2]; obtain ⟨k1, hk1⟩ := hodd1; obtain ⟨k2, hk2⟩ := hodd2; omega
    have hNClt : {x | a x ≠ 0}.ncard
        < 2 * Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := by rw [hcard1]; omega
    rcases grid_trichotomy a hadd hgap hNClt with hz | ⟨j₀, c, hc, h1, h2⟩ | ⟨i₀, c, hc, h1, h2⟩
    · exact hz
    · exact (grid_no_constant_column (by rw [← Nat.card_eq_fintype_card, hcard1]; exact h3w1)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc h1 h2).elim
    · exact (grid_no_constant_row (by rw [← Nat.card_eq_fintype_card, hcard2]; exact h3w2)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc h1 h2).elim
  · set aT : ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) → ℂ :=
      fun x => a (x.2, x.1) with haT
    have hgap : Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) + 2
        ≤ Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := by
      rw [hcard1, hcard2]; obtain ⟨k1, hk1⟩ := hodd1; obtain ⟨k2, hk2⟩ := hodd2; omega
    have haddT : ∀ q q' p p', aT (q, p) + aT (q', p') = aT (q, p') + aT (q', p) :=
      fun q q' p p' => by simp only [haT]; linear_combination hadd p p' q q'
    have hNCltT : {x | aT x ≠ 0}.ncard
        < 2 * Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := by
      have h4 : {x | aT x ≠ 0}.ncard ≤ 4 :=
        le_trans (Set.ncard_le_ncard_of_injOn Prod.swap (fun x hx => hx)
          (Prod.swap_injective.injOn) (Set.toFinite _)) hNC4
      rw [hcard2]; omega
    rcases grid_trichotomy aT haddT hgap hNCltT with hz | ⟨p₀, c, hc, h1, h2⟩ | ⟨q₀, c, hc, h1, h2⟩
    · intro pq; exact hz (pq.2, pq.1)
    · exact (grid_no_constant_row (by rw [← Nat.card_eq_fintype_card, hcard2]; exact h3w2)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc (fun q => h1 q) (fun i j hi => h2 j i hi)).elim
    · exact (grid_no_constant_column (by rw [← Nat.card_eq_fintype_card, hcard1]; exact h3w1)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc (fun p => h1 p) (fun i j hj => h2 j i hj)).elim

open scoped Classical in
/-- **Fourier reconstruction along the orthonormal `σ`-image family.**  If a class function `X`
satisfies the Parseval *equality* `⟨X, X⟩ = ∑_pq sigmaCoeff(X) pq · conj(sigmaCoeff(X) pq)` —
equivalently, `X` has no component orthogonal to `Im σ` — then `X` is recovered as its
`σ`-coefficient combination `X = ∑_pq sigmaCoeff(X) pq • χ_pq`.

Set `Y = ∑ sigmaCoeff·χ`.  Orthonormality of `chiFam` (`chiFam_spec`) makes
`⟨Y, Y⟩ = ⟨X, Y⟩ = ⟨Y, X⟩ = ∑ sigmaCoeff·conj sigmaCoeff`, the same value the Parseval hypothesis
assigns to `⟨X, X⟩`; hence `⟨X − Y, X − Y⟩ = 0`, so `X = Y` by positive-definiteness
(`eq_zero_of_inner_self_re_eq_zero`).  This is the final step the (5.8) full-column endgame needs:
once the coefficient grid is known to be a single constant full column (the abstract core
`grid_eq_const_column_of_two_col`), this lemma turns that into the class-function identity
`μ_k^{τ₁} = δ·∑_i ω_{ik}^σ`. -/
theorem eq_sum_sigmaCoeff_smul_chiFam_of_inner_self_eq (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    [Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ)] [Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {X : ClassFunction G ℂ}
    (hParseval : ClassFunction.inner X X
      = ∑ pq, hyp.sigmaCoeff hVeq app X pq * star (hyp.sigmaCoeff hVeq app X pq)) :
    X = ∑ pq, hyp.sigmaCoeff hVeq app X pq • hyp.chiFam hVeq app pq := by
  classical
  have : Finite G := Finite.of_fintype G
  -- `sigmaCoeff` is by definition `⟨X, χ_pq⟩`.
  have hXchi : ∀ pq, ClassFunction.inner X (hyp.chiFam hVeq app pq)
      = hyp.sigmaCoeff hVeq app X pq := fun _ => rfl
  set Y : ClassFunction G ℂ :=
    ∑ pq, hyp.sigmaCoeff hVeq app X pq • hyp.chiFam hVeq app pq with hY
  -- `⟨Y, Y⟩ = ∑ s·conj s` (orthonormality of `chiFam`).
  have hYY : ClassFunction.inner Y Y
      = ∑ pq, hyp.sigmaCoeff hVeq app X pq * star (hyp.sigmaCoeff hVeq app X pq) := by
    rw [hY, inner_sum_smul_sum]
    refine Finset.sum_congr rfl fun pq _ => ?_
    rw [Finset.sum_eq_single pq
      (fun ab _ hab => by
        rw [(hyp.chiFam_spec hVeq app).2.2.1, if_neg (Ne.symm hab), mul_zero])
      (fun h => absurd (Finset.mem_univ pq) h),
      (hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl, mul_one]
  -- `⟨X, Y⟩ = ∑ s·conj s`.
  have hXY : ClassFunction.inner X Y
      = ∑ pq, hyp.sigmaCoeff hVeq app X pq * star (hyp.sigmaCoeff hVeq app X pq) := by
    rw [hY, inner_sum_right]
    refine Finset.sum_congr rfl fun pq _ => ?_
    rw [OddOrder.RepresentationTheory.inner_smul_right, hXchi pq, mul_comm]
  -- `⟨Y, X⟩ = ∑ s·conj s`.
  have hYX : ClassFunction.inner Y X
      = ∑ pq, hyp.sigmaCoeff hVeq app X pq * star (hyp.sigmaCoeff hVeq app X pq) := by
    rw [hY, inner_sum_left]
    refine Finset.sum_congr rfl fun pq _ => ?_
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_conj_symm, hXchi pq]
  -- positive-definiteness on the difference `X − Y`.
  have hzero : ClassFunction.inner (X - Y) (X - Y) = 0 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hParseval, hXY, hYX, hYY]
    ring
  have hfin := eq_zero_of_inner_self_re_eq_zero (φ := X - Y)
    (by rw [hzero]; exact Complex.zero_re)
  rw [sub_eq_zero] at hfin
  exact hfin.trans hY

open scoped Classical in
/-- **Peterfalvi (5.8), `σ`-coefficient full-column endgame.**  Let `X` be a class function of `G`
that vanishes on `V` (so its `σ`-coefficient grid is additively separable, `sigmaCoeff_add_eq`),
whose `σ`-coefficients are supported on two `W₂`-columns `jcol ≠ kcol`, with column-`kcol` entries
in
`{0, δ}` and column-`jcol` entries in `{0, −δ}` (`δ = ±1`), and which accounts for its full self
inner product through its `σ`-coefficients (`hParseval`, the Parseval equality / no
`Im σ`-orthogonal
component) with `‖X‖² = w₁` (`hXnorm`, the coherence isometry).  Then `X` is a single constant full
column: either `X = δ·∑_i χ_{(i,kcol)}` or `X = −δ·∑_i χ_{(i,jcol)}`.

The abstract grid core `grid_eq_const_column_of_two_col` turns the two-column, `{0,±δ}`, mass-`w₁`
data into a single constant full coefficient column; the Fourier reconstruction
`eq_sum_sigmaCoeff_smul_chiFam_of_inner_self_eq` then turns that coefficient column back into the
class-function identity.  This is the norm-`w₁` analogue of `eq_smul_chiFam_diff_of_vanishOnV`, and
the (10.6) summed isometry `μ_k^{τ₁} = δ·∑_i ω_{ik}^σ` is the §10 application, once (5.5) supplies
the two-column support and `{0,±δ}` entries. -/
theorem eq_smul_chiFam_column_of_vanishOnV (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    [Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ)] [Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {X : ClassFunction G ℂ} (hψV : ∀ v ∈ hyp.V, X v = 0)
    {jcol kcol : (hyp.W2.subgroupOf hyp.W) →* ℂˣ} (hjk : jcol ≠ kcol)
    (hsupp : ∀ pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      pq.2 ≠ jcol → pq.2 ≠ kcol → hyp.sigmaCoeff hVeq app X pq = 0)
    {δ : ℂ} (hδ : δ = 1 ∨ δ = -1)
    (hk : ∀ p, hyp.sigmaCoeff hVeq app X (p, kcol) = 0 ∨ hyp.sigmaCoeff hVeq app X (p, kcol) = δ)
    (hj : ∀ p, hyp.sigmaCoeff hVeq app X (p, jcol) = 0 ∨ hyp.sigmaCoeff hVeq app X (p, jcol) = -δ)
    (hXnorm : ClassFunction.inner X X = (Nat.card hyp.W1 : ℂ))
    (hParseval : ClassFunction.inner X X
      = ∑ pq, hyp.sigmaCoeff hVeq app X pq * star (hyp.sigmaCoeff hVeq app X pq)) :
    (X = δ • ∑ p, hyp.chiFam hVeq app (p, kcol)) ∨
      (X = (-δ) • ∑ p, hyp.chiFam hVeq app (p, jcol)) := by
  classical
  have : Finite G := Finite.of_fintype G
  -- every coefficient is real (`{0, ±δ}` with `δ = ±1`); off the two columns it vanishes.
  have hstar : ∀ pq, star (hyp.sigmaCoeff hVeq app X pq) = hyp.sigmaCoeff hVeq app X pq := by
    intro pq
    by_cases hq : pq.2 = kcol
    · obtain ⟨p, q⟩ := pq; subst hq
      rcases hk p with h | h <;> rw [h]
      · exact star_zero _
      · rcases hδ with h' | h' <;> rw [h'] <;> simp
    · by_cases hq' : pq.2 = jcol
      · obtain ⟨p, q⟩ := pq; subst hq'
        rcases hj p with h | h <;> rw [h]
        · exact star_zero _
        · rcases hδ with h' | h' <;> rw [h'] <;> simp
      · rw [hsupp pq hq' hq, star_zero]
  -- a third column `q₀ ∉ {jcol, kcol}` exists since `w₂ ≥ 3`.
  obtain ⟨q₀, hq₀j, hq₀k⟩ : ∃ q₀ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ, q₀ ≠ jcol ∧ q₀ ≠ kcol := by
    by_contra hcon; push Not at hcon
    have hsub : (Finset.univ : Finset ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) ⊆ {jcol, kcol} := by
      intro q _
      rcases eq_or_ne q jcol with hq | hq
      · simp [hq]
      · simp [hcon q hq]
    have hcard := Finset.card_le_card hsub
    have h2 : ({jcol, kcol} : Finset ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])
    have h3 : 3 ≤ Fintype.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := by
      rw [← Nat.card_eq_fintype_card, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
      exact hyp.three_le_card_W2
    rw [Finset.card_univ] at hcard; omega
  -- the mass identity `∑ (a pq)² = |Ŵ₁| = w₁`.
  have hmass : ∑ pq, (hyp.sigmaCoeff hVeq app X pq) ^ 2
      = (Fintype.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) : ℂ) := by
    have hsq : ∀ pq, (hyp.sigmaCoeff hVeq app X pq) ^ 2
        = hyp.sigmaCoeff hVeq app X pq * star (hyp.sigmaCoeff hVeq app X pq) :=
      fun pq => by rw [hstar pq]; ring
    rw [Finset.sum_congr rfl (fun pq _ => hsq pq), ← hParseval, hXnorm,
      ← Nat.card_eq_fintype_card, hyp.card_charGroup_subgroupOf hyp.W1_le_W]
  -- apply the abstract two-column core (the grid `fun pq => sigmaCoeff X pq` beta-reduces
  -- automatically in the statement of `hcore`).
  have hcore := grid_eq_const_column_of_two_col (ι := (hyp.W1.subgroupOf hyp.W) →* ℂˣ)
    (κ := (hyp.W2.subgroupOf hyp.W) →* ℂˣ) (fun pq => hyp.sigmaCoeff hVeq app X pq)
    (fun i i' q q' => hyp.sigmaCoeff_add_eq hVeq app hψV i i' q q') hjk hq₀j hq₀k
    (fun i q hqj hqk => hsupp (i, q) hqj hqk) hδ hk hj hmass
  -- reconstruct `X` from its coefficients, then collapse to the surviving column.
  have hXrec : X = ∑ pq, hyp.sigmaCoeff hVeq app X pq • hyp.chiFam hVeq app pq :=
    hyp.eq_sum_sigmaCoeff_smul_chiFam_of_inner_self_eq hVeq app hParseval
  -- collapse the double sum onto the single nonzero column `col`, where
  -- `sigmaCoeff (·, col) = val`.
  have hcollapse : ∀ (col : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) (val : ℂ),
      (∀ p, hyp.sigmaCoeff hVeq app X (p, col) = val) →
      (∀ p q, q ≠ col → hyp.sigmaCoeff hVeq app X (p, q) = 0) →
      ∑ pq, hyp.sigmaCoeff hVeq app X pq • hyp.chiFam hVeq app pq
        = val • ∑ p, hyp.chiFam hVeq app (p, col) := by
    intro col val hcol hoff
    rw [Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single col
      (fun q _ hq => by rw [hoff p q hq, zero_smul])
      (fun h => absurd (Finset.mem_univ col) h), hcol p]
  rcases hcore with ⟨hkcol, hjcol⟩ | ⟨hjcol, hkcol⟩
  · -- column `kcol` is constantly `δ`, column `jcol` (and the rest) vanish.
    refine Or.inl ?_
    rw [hXrec, hcollapse kcol δ hkcol ?_]
    intro p q hq
    by_cases hqj : q = jcol
    · rw [hqj]; exact hjcol p
    · exact hsupp (p, q) hqj hq
  · -- column `jcol` is constantly `−δ`, column `kcol` (and the rest) vanish.
    refine Or.inr ?_
    rw [hXrec, hcollapse jcol (-δ) hjcol ?_]
    intro p q hq
    by_cases hqk : q = kcol
    · rw [hqk]; exact hkcol p
    · exact hsupp (p, q) hq hqk

end OddOrder.Peterfalvi.S05.TICyclicHypothesis


