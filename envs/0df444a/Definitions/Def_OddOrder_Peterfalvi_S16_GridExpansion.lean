-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
-- name    : OddOrder_Peterfalvi_S16_GridExpansion
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:57:15.68256+00:00
-- url     : https://prove2.me/theorems/2e7a8f44-08b2-46c3-ad0c-ae461767d483
-- title:
--   Peterfalvi (3.6)–(3.8): grid-coefficient theory of the $W$-grid
-- statement:
--   Formalizes Peterfalvi §3 (pp. 15-20) for the $\eta$-grid of §13–§16: orthonormality, the relation (3.7), and the Bessel-type vanishing of (13.19.b).
--
--   Main declarations: `eta_orthonormal` (The `η`-grid is orthonormal); `inner_eta_grid_relation` (Peterfalvi (3.7)); `inner_eta_eq_zero_of_vanish_of_inner_self_eq_two` (Peterfalvi (13.19.b)-core); `eta_diff_rigidity` (Peterfalvi (3.8) difference rigidity for the `η`-grid).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_GridExpansion.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_GridExpansion.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S05_GridRigidity

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **Peterfalvi (3.3), the trivial grid entry**: `ω₀₀ = 1_W`.  Every `w ∈ W = W₁ ⊔ W₂`
splits as `w = x·y` with `x ∈ W₁`, `y ∈ W₂` (`W` cyclic hence abelian, so the join is the
product), and the row-`0`/column-`0` trivialities (issue-2033 grid semantics) kill both
factors. -/
theorem omega_principal_eq_trivial [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    hyp.omega ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩
      = trivialClassFunction ↥hyp.W := by
  let := hyp.W_cyclic
  let : CommGroup ↥hyp.W := IsCyclic.commGroup
  have hW1le : hyp.W1 ≤ hyp.W := by
    rw [hyp.W_eq_join]; exact le_sup_left
  have hW2le : hyp.W2 ≤ hyp.W := by
    rw [hyp.W_eq_join]; exact le_sup_right
  ext w
  have hw : w ∈ (hyp.W1.subgroupOf hyp.W) ⊔ (hyp.W2.subgroupOf hyp.W) := by
    have h1 : (hyp.W1 ⊔ hyp.W2).subgroupOf hyp.W = ⊤ := by
      rw [← hyp.W_eq_join, Subgroup.subgroupOf_self]
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, h1]
    exact Subgroup.mem_top w
  obtain ⟨x, hxmem, y, hymem, hxy⟩ := Subgroup.mem_sup.mp hw
  have hval : hyp.omega ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ w = 1 := by
    rw [← hxy, hyp.omega_mul,
      hyp.omega_row_zero_apply_of_mem_W1 _ x (Subgroup.mem_subgroupOf.mp hxmem),
      hyp.omega_col_zero_apply_of_mem_W2 _ y (Subgroup.mem_subgroupOf.mp hymem),
      one_mul]
  rw [hval, trivialClassFunction_apply]

/-- **Peterfalvi (3.3)/(13.1.d): the principal `η`-entry is the trivial character** —
`η₀₀ = τ₃(ω₀₀) = τ₃(1_W) = 1_G` (`omega_principal_eq_trivial` + `tau3_trivial`), as an
equality of class functions. -/
theorem eta_principal_eq_trivial [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ = trivialClassFunction G := by
  rw [hyp.eta_eq_tau_omega, omega_principal_eq_trivial hyp, hyp.tau3_trivial]

/-- **Peterfalvi (3.3)/(13.1.d), pointwise form**: `η₀₀(g) = 1` for every `g ∈ G`. -/
theorem eta_principal_apply_eq_one [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (g : G) :
    hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ g = 1 := by
  rw [eta_principal_eq_trivial hyp, trivialClassFunction_apply]

/-- Each `η_ij = τ₃(ω_ij)` is a virtual character of `G` (`tau3_mem_ZIrr` on
`omega_mem_ZIrr`). -/
theorem eta_mem_ZIrr [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i : Fin hyp.q) (j : Fin hyp.p) :
    hyp.eta i j ∈ ZIrr G := by
  rw [hyp.eta_eq_tau_omega]
  exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr i j)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The `η`-grid is orthonormal**: `⟨η_ij, η_kl⟩ = δ_{(i,j),(k,l)}`, transported from the
`ω`-grid orthonormality (`omega_orthonormal`) through the `τ₃` isometry (`tau3_isometry`). -/
theorem eta_orthonormal [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i k : Fin hyp.q) (j l : Fin hyp.p) :
    ClassFunction.inner (hyp.eta i j) (hyp.eta k l)
      = if i = k ∧ j = l then 1 else 0 := by
  rw [hyp.eta_eq_tau_omega, hyp.eta_eq_tau_omega,
    hyp.tau3_isometry.inner_eq, hyp.omega_orthonormal]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.7)** (the `(i',j') = (0,0)` instance, which generates the general four-index
relation by arithmetic): for a class function `φ` vanishing on the conjugacy saturation of the
regular set `Ŵ = W ∖ (W₁ ∪ W₂)`,

`⟨φ, η_ij⟩ + ⟨φ, η_00⟩ = ⟨φ, η_i0⟩ + ⟨φ, η_0j⟩`.

The four-corner combination `η_ij + η_00 − η_i0 − η_0j` vanishes off `Ŵ^G`
(`eta_fourcorner_vanish` + `η_00 = 1_G`), while `φ` vanishes on `Ŵ^G`, so every summand of the
inner product dies. -/
theorem inner_eta_grid_relation [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) {φ : ClassFunction G ℂ}
    (hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))), φ x = 0)
    (i : Fin hyp.q) (j : Fin hyp.p) :
    ClassFunction.inner φ (hyp.eta i j)
        + ClassFunction.inner φ (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩)
      = ClassFunction.inner φ (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
        + ClassFunction.inner φ (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) := by
  classical
  by_cases hi : i = ⟨0, hyp.q_prime.pos⟩
  · subst hi; ring
  by_cases hj : j = ⟨0, hyp.p_prime.pos⟩
  · subst hj; ring
  -- the four-corner combination, supported on `Ŵ^G`
  have hcombo : ∀ x : G, x ∉ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))) →
      (hyp.eta i j + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩
        - hyp.eta i ⟨0, hyp.p_prime.pos⟩ - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) x = 0 := by
    intro x hx
    have h4 := hyp.eta_fourcorner_vanish i j hi hj x hx
    rw [ClassFunction.sub_apply, ClassFunction.sub_apply, ClassFunction.add_apply,
      eta_principal_apply_eq_one hyp x]
    rw [hyp.eta_eq_tau_omega i j, hyp.eta_eq_tau_omega i ⟨0, hyp.p_prime.pos⟩,
      hyp.eta_eq_tau_omega ⟨0, hyp.q_prime.pos⟩ j]
    linear_combination h4
  -- `⟨φ, c⟩ = 0`: every summand of the inner sum has a vanishing factor
  have hinner : ClassFunction.inner φ
      (hyp.eta i j + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩
        - hyp.eta i ⟨0, hyp.p_prime.pos⟩ - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum]
    have hsum : ClassFunction.innerSum φ
        (hyp.eta i j + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩
          - hyp.eta i ⟨0, hyp.p_prime.pos⟩ - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [ClassFunction.innerSum]
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : x ∈ conjClassSet
          ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))
      · rw [hvanish x hx, zero_mul]
      · rw [hcombo x hx, star_zero, mul_zero]
    rw [hsum, mul_zero]
  -- expand by conjugate-linearity in the second argument
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    ClassFunction.inner_add_right] at hinner
  linear_combination hinner

/-- **Peterfalvi (3.8), the small-support case** (pure combinatorics): a `q × p` grid `a`
(`3 ≤ q`, `3 ≤ p`) satisfying the (3.7) relation `a_ij + a_{i₀j₀} = a_{ij₀} + a_{i₀j}`
relative to some base point `(i₀, j₀)`, with at most `2` nonzero entries, is identically
zero.  In Peterfalvi's trichotomy the row/column cases (3.8.b)/(3.8.c) force at least
`min q p ≥ 3` nonzero entries, so only case (3.8.a) survives.

The proof mirrors the rank-one shift structure: an all-zero row exists (else every row
contributes a nonzero entry, `NC ≥ q ≥ 3`), which makes every row constant
(`a_ij = a_{ij₀} − a_{i₁j₀}`); a row with nonzero constant would contribute `p ≥ 3` nonzero
entries. -/
theorem grid_eq_zero_of_relation_of_card_le_two {q p : ℕ} (hq : 3 ≤ q) (hp : 3 ≤ p)
    {a : Fin q → Fin p → ℂ} (i0 : Fin q) (j0 : Fin p)
    (hrel : ∀ i j, a i j + a i0 j0 = a i j0 + a i0 j)
    (hNC : (Finset.univ.filter fun x : Fin q × Fin p => a x.1 x.2 ≠ 0).card ≤ 2) :
    ∀ i j, a i j = 0 := by
  classical
  set S : Finset (Fin q × Fin p) :=
    Finset.univ.filter fun x : Fin q × Fin p => a x.1 x.2 ≠ 0 with hS
  -- an all-zero row exists
  have hrow : ∃ i₁ : Fin q, ∀ j, a i₁ j = 0 := by
    by_contra hno
    push Not at hno
    choose f hf using hno
    have hcard : q ≤ S.card := by
      have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin q)),
          ((i, f i) : Fin q × Fin p) ∈ S := fun i _ =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf i⟩
      have := Finset.card_le_card_of_injOn
        (fun i : Fin q => ((i, f i) : Fin q × Fin p)) hmaps
        (fun i _ i' _ h => (Prod.ext_iff.mp h).1)
      simpa using this
    omega
  obtain ⟨i₁, hi₁⟩ := hrow
  -- every row is constant: `a i j = a i j₀ − a i₁ j₀`
  have hconst : ∀ i j, a i j = a i j0 - a i₁ j0 := by
    intro i j
    have h1 := hrel i j
    have h2 := hrel i₁ j
    rw [hi₁ j] at h2
    linear_combination h1 - h2
  -- a row with nonzero constant contributes `p ≥ 3` nonzero entries
  intro i j
  rw [hconst i j]
  by_contra hne
  have hcard : p ≤ S.card := by
    have hmaps : ∀ j' ∈ (Finset.univ : Finset (Fin p)),
        ((i, j') : Fin q × Fin p) ∈ S := fun j' _ =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hconst i j']; exact hne⟩
    have := Finset.card_le_card_of_injOn
      (fun j' : Fin p => ((i, j') : Fin q × Fin p)) hmaps
      (fun j' _ j'' _ h => (Prod.ext_iff.mp h).2)
    simpa using this
  omega

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.b)-core** ((3.8) applied through Bessel): a virtual character
`φ ∈ ℤ[Irr G]` with `⟨φ, φ⟩ = 2` vanishing on the conjugacy saturation of the regular set
`Ŵ = W ∖ (W₁ ∪ W₂)` is orthogonal to the entire `η`-grid.

This is Peterfalvi's `NC(ψ) ≤ ‖ψ‖² = 2 < 2q` step: the grid coefficients
`a_ij = ⟨φ, η_ij⟩` are integers (`inner_mem_ZIrr_int`), the orthogonal projection onto the
(orthonormal) grid satisfies Bessel `∑ a_ij² ≤ ⟨φ, φ⟩ = 2`, so at most two coefficients are
nonzero; the (3.7) relation (`inner_eta_grid_relation`) then forces all of them to vanish
(`grid_eq_zero_of_relation_of_card_le_two`, using `3 ≤ q` and `3 ≤ p`).

Consumed with `φ = (ψ − ψ̄)^τ` for an irreducible `ψ` of a type-I family (Peterfalvi
(13.19.b), the `L^{τ₁} ⊥ η_ij` fact behind the (14.11.2)/(14.16) signed expansions). -/
theorem inner_eta_eq_zero_of_vanish_of_inner_self_eq_two [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) {φ : ClassFunction G ℂ}
    (hφZ : φ ∈ ZIrr G)
    (hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))), φ x = 0)
    (hnorm : ClassFunction.inner φ φ = 2) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner φ (hyp.eta i j) = 0 := by
  classical
  -- integer coefficient grid
  have hint : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ∃ m : ℤ, ClassFunction.inner φ (hyp.eta i j) = (m : ℂ) := fun i j =>
    ClassFunction.inner_mem_ZIrr_int hφZ (eta_mem_ZIrr hyp i j)
  choose m hm using hint
  -- the grid projection and its residual
  set X : ClassFunction G ℂ :=
    ∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j : ℂ) • hyp.eta i j with hX
  set Y : ClassFunction G ℂ := φ - X with hY
  -- `⟨X, η_kl⟩ = m k l` by orthonormality
  have hXeta : ∀ (k : Fin hyp.q) (l : Fin hyp.p),
      ClassFunction.inner X (hyp.eta k l) = (m k l : ℂ) := by
    intro k l
    rw [hX, inner_sum_left]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun i _ hik => ?_)]
    · rw [inner_sum_left,
        Finset.sum_eq_single_of_mem l (Finset.mem_univ _) (fun j _ hjl => ?_)]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
          if_pos ⟨rfl, rfl⟩, mul_one]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
          if_neg (by rintro ⟨-, rfl⟩; exact hjl rfl), mul_zero]
    · rw [inner_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
        if_neg (by rintro ⟨rfl, -⟩; exact hik rfl), mul_zero]
  -- `⟨Y, η_kl⟩ = 0`
  have hYeta : ∀ (k : Fin hyp.q) (l : Fin hyp.p),
      ClassFunction.inner Y (hyp.eta k l) = 0 := by
    intro k l
    rw [hY, ClassFunction.inner_sub_left, hXeta k l, hm k l, sub_self]
  -- `⟨φ, X⟩ = ∑ m²` and `⟨X, X⟩ = ∑ m²`
  have hsum_sq : ∀ ψ : ClassFunction G ℂ,
      (∀ (k : Fin hyp.q) (l : Fin hyp.p),
        ClassFunction.inner ψ (hyp.eta k l) = (m k l : ℂ)) →
      ClassFunction.inner ψ X
        = ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) := by
    intro ψ hψ
    rw [hX, inner_sum_right]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_right, hψ i j, star_intCast]
    ring
  -- `⟨X, Y⟩ = 0` and `⟨Y, X⟩ = 0`
  have hXY : ClassFunction.inner X Y = 0 := by
    have h := hsum_sq X hXeta
    have h2 : ClassFunction.inner X φ
        = ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hsum_sq φ hm]
      rw [star_intCast]
    rw [hY, ClassFunction.inner_sub_right, h2, h, sub_self]
  have hYX : ClassFunction.inner Y X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXY, star_zero]
  -- Pythagorean split: `⟨φ, φ⟩ = ∑ m² + ⟨Y, Y⟩`
  have hsplit : ClassFunction.inner φ φ
      = ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ)
        + ClassFunction.inner Y Y := by
    have hφXY : φ = X + Y := by rw [hY]; abel
    calc ClassFunction.inner φ φ
        = ClassFunction.inner (X + Y) (X + Y) := by rw [← hφXY]
      _ = ClassFunction.inner X X + ClassFunction.inner X Y
          + (ClassFunction.inner Y X + ClassFunction.inner Y Y) := by
          rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
            ClassFunction.inner_add_right]
      _ = ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ)
          + ClassFunction.inner Y Y := by
          rw [hXY, hYX, hsum_sq X hXeta]; ring
  -- `⟨Y, Y⟩` is a nonnegative real, so `∑ m² ≤ 2` over `ℤ`
  have hYY : ∃ r : ℝ, 0 ≤ r ∧ ClassFunction.inner Y Y = (r : ℂ) := by
    refine ⟨(Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (Y g), ?_,
      inner_self_eq_realCast Y⟩
    have hsum : (0 : ℝ) ≤ ∑ g : G, Complex.normSq (Y g) :=
      Finset.sum_nonneg fun g _ => Complex.normSq_nonneg _
    positivity
  obtain ⟨r, hr0, hr⟩ := hYY
  have hsq_le : ∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 ≤ 2 := by
    have h2 : ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) + (r : ℂ)
        = (2 : ℂ) := by rw [← hr, ← hsplit, hnorm]
    have hreal : ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℝ) + r
        = 2 := by
      have hre := congrArg Complex.re h2
      simp only [Complex.add_re, Complex.intCast_re, Complex.ofReal_re] at hre
      norm_num at hre
      exact_mod_cast hre
    have : ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℝ) ≤ 2 := by
      linarith
    exact_mod_cast this
  -- at most two nonzero coefficients
  have hNC : (Finset.univ.filter
      fun x : Fin hyp.q × Fin hyp.p => ((m x.1 x.2 : ℂ) ≠ 0)).card ≤ 2 := by
    have hcard_le : ((Finset.univ.filter
        fun x : Fin hyp.q × Fin hyp.p => ((m x.1 x.2 : ℂ) ≠ 0)).card : ℤ)
        ≤ ∑ x : Fin hyp.q × Fin hyp.p, (m x.1 x.2) ^ 2 :=
      calc ((Finset.univ.filter
            fun x : Fin hyp.q × Fin hyp.p => ((m x.1 x.2 : ℂ) ≠ 0)).card : ℤ)
          = ∑ x ∈ Finset.univ.filter
              (fun x : Fin hyp.q × Fin hyp.p => ((m x.1 x.2 : ℂ) ≠ 0)), 1 := by
            simp
        _ ≤ ∑ x ∈ Finset.univ.filter
              (fun x : Fin hyp.q × Fin hyp.p => ((m x.1 x.2 : ℂ) ≠ 0)),
                (m x.1 x.2) ^ 2 := by
            refine Finset.sum_le_sum fun x hx => ?_
            have hne : m x.1 x.2 ≠ 0 := by
              intro h0
              exact (Finset.mem_filter.mp hx).2 (by rw [h0, Int.cast_zero])
            nlinarith [Int.one_le_abs hne, sq_abs (m x.1 x.2)]
        _ ≤ ∑ x : Fin hyp.q × Fin hyp.p, (m x.1 x.2) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun x _ _ => sq_nonneg _)
    have hprod : ∑ x : Fin hyp.q × Fin hyp.p, (m x.1 x.2) ^ 2
        = ∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 := by
      rw [Fintype.sum_prod_type]
    omega
  -- the (3.7) relation on the coefficient grid, then rigidity
  have hrel : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      (m i j : ℂ) + (m ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ : ℂ)
        = (m i ⟨0, hyp.p_prime.pos⟩ : ℂ) + (m ⟨0, hyp.q_prime.pos⟩ j : ℂ) := by
    intro i j
    have h := inner_eta_grid_relation hyp hvanish i j
    rw [hm, hm, hm, hm] at h
    exact h
  have hzero := grid_eq_zero_of_relation_of_card_le_two
    hyp.three_le_q hyp.three_le_p
    ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ hrel hNC
  intro i j
  rw [hm i j, hzero i j]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.8) difference rigidity for the `η`-grid** (`eq_signed_sub_cTIiso`, Coq
`PFsection3.v`).  A virtual character `X ∈ ℤ[Irr G]` with `‖X‖² = 2` that agrees with a signed
row-difference `s·(η_{i₀j₁} − η_{i₀j₂})` (`s = ±1`, `j₁ ≠ j₂`) on the conjugacy saturation of the
regular set `Ŵ = W ∖ (W₁ ∪ W₂)` equals it: `X = s·(η_{i₀j₁} − η_{i₀j₂})`.

Where `inner_eta_eq_zero_of_vanish_of_inner_self_eq_two` handles the `NC ≤ 2` *all-zero* case, this
is the `NC(ψ) ≤ 4` *difference* case: it feeds the abstract engine
`S05.orthonormalGrid_diff_rigidity` (full (3.8) trichotomy, constant-row/column excluded) with the
`η`-grid data — orthonormality (`eta_orthonormal`), virtual-character membership (`eta_mem_ZIrr`),
the coprime-odd axis sizes `q, p ≥ 3`, and the (3.7) separability of
`ψ = X − s·(η_{i₀j₁} − η_{i₀j₂})` (assembled from four instances of `inner_eta_grid_relation`,
valid because `ψ` vanishes on `Ŵ^G`).

This is the row-`0` shape (`i₀ = 0`) behind the (13.18) `S`-side cross-relation
`τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}`, and the general row/column shape used by Peterfalvi
(4.8)/(10.5)/(10.10)/(11.8). -/
theorem eta_diff_rigidity [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {X : ClassFunction G ℂ} (hXZ : X ∈ ZIrr G) (hX2 : ClassFunction.inner X X = 2)
    (i0 : Fin hyp.q) {j1 j2 : Fin hyp.p} (hj : j1 ≠ j2) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hvanish : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (X - (s : ℂ) • (hyp.eta i0 j1 - hyp.eta i0 j2)) x = 0) :
    X = (s : ℂ) • (hyp.eta i0 j1 - hyp.eta i0 j2) := by
  classical
  have hcardq : Nat.card (Fin hyp.q) = hyp.q :=
    Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
  have hcardp : Nat.card (Fin hyp.p) = hyp.p :=
    Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
  -- (3.7) separability of the `ψ`-coefficient grid, from four `inner_eta_grid_relation` instances.
  have hsep : ∀ (i i' : Fin hyp.q) (j j' : Fin hyp.p),
      ClassFunction.inner (X - (s : ℂ) • (hyp.eta i0 j1 - hyp.eta i0 j2))
          ((fun pq : Fin hyp.q × Fin hyp.p => hyp.eta pq.1 pq.2) (i, j))
        + ClassFunction.inner (X - (s : ℂ) • (hyp.eta i0 j1 - hyp.eta i0 j2))
            ((fun pq : Fin hyp.q × Fin hyp.p => hyp.eta pq.1 pq.2) (i', j'))
      = ClassFunction.inner (X - (s : ℂ) • (hyp.eta i0 j1 - hyp.eta i0 j2))
            ((fun pq : Fin hyp.q × Fin hyp.p => hyp.eta pq.1 pq.2) (i, j'))
        + ClassFunction.inner (X - (s : ℂ) • (hyp.eta i0 j1 - hyp.eta i0 j2))
            ((fun pq : Fin hyp.q × Fin hyp.p => hyp.eta pq.1 pq.2) (i', j)) := by
    intro i i' j j'
    have h1 := inner_eta_grid_relation hyp hvanish i j
    have h2 := inner_eta_grid_relation hyp hvanish i' j'
    have h3 := inner_eta_grid_relation hyp hvanish i j'
    have h4 := inner_eta_grid_relation hyp hvanish i' j
    simp only
    linear_combination h1 + h2 - h3 - h4
  have hmain := OddOrder.Peterfalvi.S05.orthonormalGrid_diff_rigidity
    (fun pq : Fin hyp.q × Fin hyp.p => hyp.eta pq.1 pq.2)
    (fun pq => eta_mem_ZIrr hyp pq.1 pq.2)
    (fun a => by simpa using eta_orthonormal hyp a.1 a.1 a.2 a.2)
    (fun a b hab => by
      rw [eta_orthonormal hyp a.1 b.1 a.2 b.2, if_neg ?_]
      rintro ⟨h1, h2⟩; exact hab (Prod.ext h1 h2))
    (by rw [hcardq]; exact hyp.three_le_q) (by rw [hcardp]; exact hyp.three_le_p)
    (by rw [hcardq]; exact hyp.q_odd) (by rw [hcardp]; exact hyp.p_odd)
    (by rw [hcardq, hcardp]
        exact (Nat.coprime_primes hyp.q_prime hyp.p_prime).mpr (Ne.symm hyp.p_ne_q))
    hXZ hX2 (P1 := (i0, j1)) (P2 := (i0, j2))
    (by intro h; exact hj (Prod.ext_iff.mp h).2) hs hsep
  simpa using hmain

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.8) difference rigidity, column form** (issue 2035 #86, the de-swap of the
`T`-side cross-relation): the same abstract engine as `eta_diff_rigidity`
(`S05.orthonormalGrid_diff_rigidity` takes arbitrary distinct grid points), instantiated at a
fixed *column* `j₀` with distinct rows `i₁ ≠ i₂`.  This is the `T`-side
column-fixed/row-difference shape consumed by `tauT_nu_cross` directly at `hyp` — previously
obtained by transposing through an older asymmetric `Hypothesis.swap` interface. -/
theorem eta_diff_rigidity_col [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {X : ClassFunction G ℂ} (hXZ : X ∈ ZIrr G) (hX2 : ClassFunction.inner X X = 2)
    {i1 i2 : Fin hyp.q} (hi : i1 ≠ i2) (j0 : Fin hyp.p) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hvanish : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (X - (s : ℂ) • (hyp.eta i1 j0 - hyp.eta i2 j0)) x = 0) :
    X = (s : ℂ) • (hyp.eta i1 j0 - hyp.eta i2 j0) := by
  classical
  have hcardq : Nat.card (Fin hyp.q) = hyp.q :=
    Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
  have hcardp : Nat.card (Fin hyp.p) = hyp.p :=
    Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
  have hsep : ∀ (i i' : Fin hyp.q) (j j' : Fin hyp.p),
      ClassFunction.inner (X - (s : ℂ) • (hyp.eta i1 j0 - hyp.eta i2 j0))
          ((fun pq : Fin hyp.q × Fin hyp.p => hyp.eta pq.1 pq.2) (i, j))
        + ClassFunction.inner (X - (s : ℂ) • (hyp.eta i1 j0 - hyp.eta i2 j0))
            ((fun pq : Fin hyp.q × Fin hyp.p => hyp.eta pq.1 pq.2) (i', j'))
      = ClassFunction.inner (X - (s : ℂ) • (hyp.eta i1 j0 - hyp.eta i2 j0))
            ((fun pq : Fin hyp.q × Fin hyp.p => hyp.eta pq.1 pq.2) (i, j'))
        + ClassFunction.inner (X - (s : ℂ) • (hyp.eta i1 j0 - hyp.eta i2 j0))
            ((fun pq : Fin hyp.q × Fin hyp.p => hyp.eta pq.1 pq.2) (i', j)) := by
    intro i i' j j'
    have h1 := inner_eta_grid_relation hyp hvanish i j
    have h2 := inner_eta_grid_relation hyp hvanish i' j'
    have h3 := inner_eta_grid_relation hyp hvanish i j'
    have h4 := inner_eta_grid_relation hyp hvanish i' j
    simp only
    linear_combination h1 + h2 - h3 - h4
  have hmain := OddOrder.Peterfalvi.S05.orthonormalGrid_diff_rigidity
    (fun pq : Fin hyp.q × Fin hyp.p => hyp.eta pq.1 pq.2)
    (fun pq => eta_mem_ZIrr hyp pq.1 pq.2)
    (fun a => by simpa using eta_orthonormal hyp a.1 a.1 a.2 a.2)
    (fun a b hab => by
      rw [eta_orthonormal hyp a.1 b.1 a.2 b.2, if_neg ?_]
      rintro ⟨h1, h2⟩; exact hab (Prod.ext h1 h2))
    (by rw [hcardq]; exact hyp.three_le_q) (by rw [hcardp]; exact hyp.three_le_p)
    (by rw [hcardq]; exact hyp.q_odd) (by rw [hcardp]; exact hyp.p_odd)
    (by rw [hcardq, hcardp]
        exact (Nat.coprime_primes hyp.q_prime hyp.p_prime).mpr (Ne.symm hyp.p_ne_q))
    hXZ hX2 (P1 := (i1, j0)) (P2 := (i2, j0))
    (by intro h; exact hi (Prod.ext_iff.mp h).1) hs hsep
  simpa using hmain

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **A norm-one virtual character is a signed irreducible.**  If `φ ∈ ℤ[Irr G]` has
`⟨φ, φ⟩ = 1`, then `φ = ε • χ` for a single irreducible `χ` and a sign `ε = ±1`.  Its
integer Fourier coefficients sum of squares equals `1`, so exactly one is nonzero and it
is `±1`.  This is the `dirr` primitive used to turn the (3.8) rigidity output
`⟨ψ^{τ₁} − ψ̄^{τ₁}, η_ij⟩ = 0` into the individual orthogonality `⟨η_ij, ψ^{τ₁}⟩ = 0`. -/
theorem exists_sign_irr_of_inner_self_one [Finite G] {φ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) (hnorm : ClassFunction.inner φ φ = 1) :
    ∃ (χ : IrreducibleCharacter G) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      φ = (ε : ℂ) • (χ : ClassFunction G ℂ) := by
  classical
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  have hsumC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 1 := hsq.symm.trans hnorm
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = 1 := by exact_mod_cast hsumC
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  have hge : ∀ a ∈ c.support, 1 ≤ c a ^ 2 := fun a ha => by
    have h := Int.one_le_abs (hne a ha)
    calc (1 : ℤ) = 1 ^ 2 := by ring
      _ ≤ |c a| ^ 2 := by gcongr
      _ = c a ^ 2 := sq_abs (c a)
  have hcard1 : c.support.card = 1 := by
    have hle : (c.support.card : ℤ) ≤ ∑ a ∈ c.support, c a ^ 2 :=
      calc (c.support.card : ℤ) = ∑ _a ∈ c.support, (1 : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ a ∈ c.support, c a ^ 2 := Finset.sum_le_sum hge
    rw [hsumZ] at hle
    have hpos : 0 < c.support.card := by
      rw [Finset.card_pos]
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty] at hsumZ
      exact absurd hsumZ (by norm_num)
    omega
  obtain ⟨α₀, hα0eq⟩ := Finset.card_eq_one.mp hcard1
  have hα0mem : α₀ ∈ irreducibleCharacters G := hsupp (by rw [hα0eq]; simp)
  rw [hα0eq, Finset.sum_singleton] at hrepr
  rw [hα0eq, Finset.sum_singleton] at hsumZ
  have hcα : c α₀ = 1 ∨ c α₀ = -1 := by
    rw [pow_two] at hsumZ; exact mul_self_eq_one_iff.mp hsumZ
  exact ⟨⟨α₀, hα0mem⟩, c α₀, hcα, by rw [hrepr]⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.b), the cross-group grid orthogonality** (engine + `dirr` finish;
the Dade support-vanishing is the one named §13/§14 hypothesis).

Let `ψ^{τ₁}` (`psi`) and `ψ̄^{τ₁}` (`psiConj`) be two distinct norm-one virtual characters of
`G` (the `τ₁`-images of an irreducible `ψ ∈ ℒ` of a type-`I` maximal subgroup and its complex
conjugate; distinctness `⟨ψ^{τ₁}, ψ̄^{τ₁}⟩ = 0` reflects `ψ ≠ ψ̄`).  If the difference
`ψ^{τ₁} − ψ̄^{τ₁}` vanishes on the conjugacy saturation of the regular set `Ŵ = W ∖ (W₁ ∪ W₂)`
(Peterfalvi (13.19.a): `Ã(L)` avoids `P^G ∪ W^G`, so `(ψ − ψ̄)^τ` is supported off `Ŵ^G`),
then `ψ^{τ₁}` is orthogonal to the whole `η`-grid.

The difference has squared norm `2`, so the (3.8) rigidity engine gives
`⟨ψ^{τ₁} − ψ̄^{τ₁}, η_ij⟩ = 0`; the `dirr` finish (each of `ψ^{τ₁}`, `ψ̄^{τ₁}`, `η_ij` is a
signed irreducible, `exists_sign_irr_of_inner_self_one`) upgrades this to the individual
orthogonality: a nonzero `⟨η_ij, ψ^{τ₁}⟩` would force `ψ^{τ₁}` and `ψ̄^{τ₁}` to share the
constituent `χ_{η_ij}`, contradicting `ψ^{τ₁} ≠ ψ̄^{τ₁}`. -/
theorem eta_orthogonal_of_norm_one_pair_vanish [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {psi psiConj : ClassFunction G ℂ}
    (hpsiZ : psi ∈ ZIrr G) (hconjZ : psiConj ∈ ZIrr G)
    (hpsi1 : ClassFunction.inner psi psi = 1)
    (hconj1 : ClassFunction.inner psiConj psiConj = 1)
    (hcross : ClassFunction.inner psi psiConj = 0)
    (hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))), (psi - psiConj) x = 0) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j) psi = 0 := by
  classical
  -- the difference `Ψ = ψ^{τ₁} − ψ̄^{τ₁}` is a norm-2 virtual character
  have hPsiZ : psi - psiConj ∈ ZIrr G := (ZIrr G).sub_mem hpsiZ hconjZ
  have hcross' : ClassFunction.inner psiConj psi = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcross, star_zero]
  have hPsi2 : ClassFunction.inner (psi - psiConj) (psi - psiConj) = 2 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hpsi1, hconj1, hcross, hcross']
    ring
  -- engine: `Ψ ⊥ η_ij` for all `i, j`
  have hengine := inner_eta_eq_zero_of_vanish_of_inner_self_eq_two hyp hPsiZ hvanish hPsi2
  -- signed-irreducible decompositions of `ψ^{τ₁}`, `ψ̄^{τ₁}`
  obtain ⟨χp, εp, hεp, hpeq⟩ := exists_sign_irr_of_inner_self_one hpsiZ hpsi1
  obtain ⟨χc, εc, hεc, hceq⟩ := exists_sign_irr_of_inner_self_one hconjZ hconj1
  -- distinct constituents: `χp ≠ χc`
  have hp0 : (εp : ℂ) ≠ 0 := by rcases hεp with h | h <;> rw [h] <;> norm_num
  have hc0 : (εc : ℂ) ≠ 0 := by rcases hεc with h | h <;> rw [h] <;> norm_num
  have hχne : χp ≠ χc := by
    intro heq
    have hval2 : ClassFunction.inner psi psiConj = (εp : ℂ) * (εc : ℂ) := by
      rw [hpeq, hceq, ClassFunction.inner_smul_left,
        OddOrder.RepresentationTheory.inner_smul_right,
        OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite, if_pos heq,
        star_intCast, mul_one]
    rw [hval2] at hcross
    exact (mul_ne_zero hp0 hc0) hcross
  -- individual orthogonality
  intro i j
  -- `η_ij` is a signed irreducible
  obtain ⟨χη, εη, hεη, hηeq⟩ := exists_sign_irr_of_inner_self_one (eta_mem_ZIrr hyp i j)
    (by simpa using eta_orthonormal hyp i i j j)
  -- `⟨η_ij, ψ^{τ₁}⟩ = ε_η ε_p · [χ_η = χ_p]`
  have hval : ∀ (χ : IrreducibleCharacter G) (ε : ℤ),
      ClassFunction.inner (hyp.eta i j) ((ε : ℂ) • (χ : ClassFunction G ℂ))
        = (εη : ℂ) * (ε : ℂ) * (if χη = χ then (1 : ℂ) else 0) := by
    intro χ ε
    rw [hηeq, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite]
    rw [star_intCast]; ring
  -- engine relation at `(i, j)`: `⟨η_ij, ψ^{τ₁}⟩ = ⟨η_ij, ψ̄^{τ₁}⟩`
  have hrel : ClassFunction.inner (hyp.eta i j) psi
      = ClassFunction.inner (hyp.eta i j) psiConj := by
    have h0 : ClassFunction.inner (hyp.eta i j) (psi - psiConj) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hengine i j, star_zero]
    rwa [ClassFunction.inner_sub_right, sub_eq_zero] at h0
  by_contra hnz
  rw [hpeq] at hnz hrel
  rw [hceq] at hrel
  rw [hval χp εp] at hnz hrel
  rw [hval χc εc] at hrel
  -- nonzero forces `χη = χp`; the relation then forces `χη = χc`; contradiction
  have hp_eq : χη = χp := by
    by_contra hpne; rw [if_neg hpne, mul_zero] at hnz; exact hnz rfl
  rw [if_pos hp_eq] at hnz hrel
  have hc_eq : χη = χc := by
    by_contra hcne
    rw [if_neg hcne, mul_zero] at hrel
    exact hnz hrel
  exact hχne (hp_eq ▸ hc_eq)

end OddOrder.Peterfalvi.S16


