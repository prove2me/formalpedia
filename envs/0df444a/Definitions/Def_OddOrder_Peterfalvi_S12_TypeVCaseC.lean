-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_TypeVCaseC
-- name    : OddOrder_Peterfalvi_S12_TypeVCaseC
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:27:12.191735+00:00
-- url     : https://prove2.me/theorems/005cc23d-13a1-4708-9f1f-40bf8930e8fc
-- title:
--   Peterfalvi (10.10.2): the type V case (c) structural package
-- statement:
--   Formalizes the structural step (10.10.2) of the proof of Theorem (10.10) for case (c) of Definition (8.7) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §10, pp. 62-63), including the $S_1$-count.
--
--   Main declarations: `Hypothesis.w1_mul_SHCcount_add_one_eq_of_card_eq_prime_cube` (Peterfalvi (10.10.2), the exact `S₁`-count `|S₁| = (p² − 1)/w₁`); `Hypothesis.SHCcount_eq_of_card_eq_prime_cube` (Peterfalvi (10.10.2), the case-(c) `S₁`-count `|S₁| = 4(w₁ − 1)`); `Hypothesis.eight_le_SHCcount_of_card_eq_prime_cube` (Peterfalvi (10.10.2), the `h8` count `|S₁| = 4(w₁ − 1) ≥ 8`); `Hypothesis.linear_of_induce_isIrreducible_of_card_eq_prime_cube` (Peterfalvi (10.10.2), linearity of irreducibly-inducing sources).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_TypeVCaseC.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_TypeVCaseC.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_TypeVColumnCoherence

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **Peterfalvi (10.10.2), the abelianization order**: a non-abelian group of order `p³` has
`|K/K′| = p²`.  Book: "Since `H` is a non-abelian group of order `p³`, `H′ = Z(H)` has order
`p`" — this is `IsExtraspecial.of_card_eq_prime_cube` (which also gives `K′ = Z(K)`), and
`|K| = |K/K′|·|K′|` leaves `|K/K′| = p³/p = p²`.  This is the order of `H/H′` behind the
`S₁`-count `(|H : H′| − 1)/w₁ = (p² − 1)/w₁` of (10.10.2). -/
theorem card_abelianization_eq_prime_sq_of_card_eq_prime_cube {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card K = p ^ 3)
    (hnonab : ¬ IsMulCommutative K) :
    Nat.card (Abelianization K) = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hext : IsExtraspecial p K :=
    IsExtraspecial.of_card_eq_prime_cube hcard fun hcomm => hnonab ⟨⟨hcomm⟩⟩
  have hcomm_card : Nat.card ↥(commutator K) = p := hext.commutator_card
  have heq := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator K)
  rw [hcard, hcomm_card] at heq
  have habel : Nat.card (Abelianization K) = Nat.card (K ⧸ commutator K) := rfl
  have hmul : Nat.card (K ⧸ commutator K) * p = p ^ 2 * p := by rw [← heq]; ring
  rw [habel]
  exact Nat.eq_of_mul_eq_mul_right hp.pos hmul

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.2), the exact `S₁`-count `|S₁| = (p² − 1)/w₁`** (book: "`S₁` consists of
`(|H : H′| − 1)/w₁ = (p² − 1)/w₁` irreducible characters of degree `w₁`"), stated in the cleared
form `w₁·|S₁| + 1 = p²` to avoid natural-number division.

`S₁` is realized as the degree-`w₁` irreducible members of `S = inducedFamily M`.  Combines the
(11.8.1) orbit count `|M′/M″| = w₁·|S₁| + 1`
(`card_abelianization_derived_eq_w1_mul_card_SHCSet_add_one`) with the abelianization order
`|M′/M″| = |H : H′| = p²` for the non-abelian `|M′| = p³`
(`card_abelianization_eq_prime_sq_of_card_eq_prime_cube`).  Needs neither (10.10.1) nor `w₁ ≥ 3`. -/
theorem Hypothesis.w1_mul_SHCcount_add_one_eq_of_card_eq_prime_cube [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card ↥((derivedInG M).subgroupOf M) = p ^ 3)
    (hnonab : ¬ IsMulCommutative ↥((derivedInG M).subgroupOf M)) :
    hyp.w1 * (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card + 1 = p ^ 2 := by
  have := hyp.finiteG
  classical
  have horbit := hyp.card_abelianization_derived_eq_w1_mul_card_SHCSet_add_one hG
  rw [card_abelianization_eq_prime_sq_of_card_eq_prime_cube hp hcard hnonab] at horbit
  exact horbit.symm

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.2), the case-(c) `S₁`-count `|S₁| = 4(w₁ − 1)`**: substituting the
(10.10.1) pin `p = 2w₁ − 1` into the exact count `w₁·|S₁| + 1 = p²`
(`w1_mul_SHCcount_add_one_eq_of_card_eq_prime_cube`) gives `w₁·|S₁| = 4w₁² − 4w₁`, i.e.
`|S₁| = 4w₁ − 4`. -/
theorem Hypothesis.SHCcount_eq_of_card_eq_prime_cube [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card ↥((derivedInG M).subgroupOf M) = p ^ 3)
    (hnonab : ¬ IsMulCommutative ↥((derivedInG M).subgroupOf M))
    (hp2w1 : (p : ℤ) = 2 * (hyp.w1 : ℤ) - 1) (hw13 : 3 ≤ hyp.w1) :
    ((Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card : ℤ) = 4 * (hyp.w1 : ℤ) - 4 := by
  have := hyp.finiteG
  classical
  have hZ : (p : ℤ) ^ 2 = (hyp.w1 : ℤ)
      * ((Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
          (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
            (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card : ℤ) + 1 := by
    exact_mod_cast (hyp.w1_mul_SHCcount_add_one_eq_of_card_eq_prime_cube hG hp hcard hnonab).symm
  rw [hp2w1] at hZ
  have hw13' : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw13
  have hw1ne : (hyp.w1 : ℤ) ≠ 0 := by omega
  refine mul_left_cancel₀ hw1ne ?_
  linear_combination -hZ

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.2), the `h8` count `|S₁| = 4(w₁ − 1) ≥ 8`**: with `|M′| = p³`
non-abelian and `p = 2w₁ − 1` ((10.10.1)), the degree-`w₁` irreducible members of `S`
number `|S₁| = (p² − 1)/w₁ = 4(w₁ − 1) ≥ 8` (for `w₁ ≥ 3`).  Numeric corollary of the exact
count `SHCcount_eq_of_card_eq_prime_cube`; it discharges the `h8` input of
`typeV_caseC_coherence_engine` and of the (10.10.3) computations. -/
theorem Hypothesis.eight_le_SHCcount_of_card_eq_prime_cube [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card ↥((derivedInG M).subgroupOf M) = p ^ 3)
    (hnonab : ¬ IsMulCommutative ↥((derivedInG M).subgroupOf M))
    (hp2w1 : (p : ℤ) = 2 * (hyp.w1 : ℤ) - 1) (hw13 : 3 ≤ hyp.w1) :
    8 ≤ (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card := by
  have := hyp.finiteG
  classical
  have hcardeq := hyp.SHCcount_eq_of_card_eq_prime_cube hG hp hcard hnonab hp2w1 hw13
  have hw13' : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw13
  have h8 : (8 : ℤ) ≤ ((Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card : ℤ) := by omega
  exact_mod_cast h8

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.2), linearity of irreducibly-inducing sources**: for `H = M′`
non-abelian of order `p³` (`p = w₂`), a `θ ∈ Irr M′` whose induction `Ind_{M′}^M θ` is
*irreducible* is linear, `θ(1) = 1` (no nontriviality needed: `θ(1) = 1` holds for the
trivial `θ` outright).

Book: "If `θ ∈ Irr H`, then `θ(1)` divides `p³` but `θ(1)² ≤ p³`, whence `θ(1) = 1` or
`θ(1) = p`. ... Then `∑_{0<j<p} θ_j(1)² = (p − 1)p² = |H| − |H : H′|`.  Thus
`S − S₁ = {μ_j | 0 < j < p}`."  Counting form of that exhaustion: the reducible-inducing
sources are exactly the `w₂ = p` certain-type columns `χ_j`
(`card_reducible_induce_eq_W2`); the trivial column is the trivial character
(`chiRestrict_one_eq_trivial`) and no nontrivial *linear* source induces reducibly
(`inertia_eq_derived_of_linear` + [Is] 6.34), so the `p − 1` nontrivial columns are
nonlinear.  The nonlinear sources number exactly `p − 1`: degrees are `p`-powers `p^k`
(`exists_characterDegree_eq_prime_pow_of_isPGroup`) with `p^{2k} ≤ ∑_θ θ(1)² = p³`
(`sumIrreducibleDegreeSq`), so nonlinear degrees are `p`, and the Burnside sum
`p² + #NL·p² = p³` (linear count `= |M′{}^{ab}| = p²`,
`card_filter_degree_one_eq_card_abelianization` +
`card_abelianization_eq_prime_sq_of_card_eq_prime_cube`) gives `#NL = p − 1`.  Hence
*every* nonlinear source is a column and induces reducibly; contrapositively an
irreducibly-inducing source is linear. -/
theorem Hypothesis.linear_of_induce_isIrreducible_of_card_eq_prime_cube [Finite G]
    {M : Subgroup G} (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {p : ℕ} (hp : p.Prime) (hpw2 : p = hyp.w2)
    (hcard : Nat.card ↥((derivedInG M).subgroupOf M) = p ^ 3)
    (hnonab : ¬ IsMulCommutative ↥((derivedInG M).subgroupOf M))
    {θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M)}
    (hirr : IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ))) :
    (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1 := by
  have := hyp.finiteG
  have : Fact p.Prime := ⟨hp⟩
  classical
  -- the §6 certain-type hypothesis and its instances (as in
  -- `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum`)
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  let : Fintype ↥M := Fintype.ofFinite _
  let : Fintype ↥h.K := Fintype.ofFinite _
  let : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  -- natural degrees `dg` on `Irr M′`
  choose dg dgpos hdgeq using fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
    irreducibleCharacter_apply_one_eq_pos_natCast χ
  -- Burnside degree-sum: `∑ dg² = p³`
  have hpg : IsPGroup p ↥((derivedInG M).subgroupOf M) := IsPGroup.of_card hcard
  have hsumC := OddOrder.RepresentationTheory.sumIrreducibleDegreeSq
    (G := ↥((derivedInG M).subgroupOf M))
  rw [hcard] at hsumC
  have hsum : ∑ χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M), dg χ ^ 2
      = p ^ 3 := by
    have hC : ((∑ χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M), dg χ ^ 2 : ℕ) : ℂ)
        = ((p ^ 3 : ℕ) : ℂ) := by
      rw [Nat.cast_sum, ← hsumC]
      exact Finset.sum_congr rfl fun χ _ => by rw [Nat.cast_pow, hdgeq χ]
    exact_mod_cast hC
  -- degree dichotomy: nonlinear degrees are `p` (a `p`-power `p^k`, `k ≥ 1`, `2k ≤ 3`)
  have hdg_nl : ∀ χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M),
      ¬ (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1 → dg χ = p := by
    intro χ hχ
    obtain ⟨k, hk⟩ :=
      OddOrder.Peterfalvi.S03.exists_characterDegree_eq_prime_pow_of_isPGroup hpg χ
    have hdgk : dg χ = p ^ k := by
      have hcast : ((dg χ : ℕ) : ℂ) = ((p ^ k : ℕ) : ℂ) := by
        rw [← hdgeq χ, Nat.cast_pow]
        exact hk
      exact_mod_cast hcast
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hdgk
      exact hχ (by rw [hdgeq χ, hdgk, Nat.cast_one])
    have hle : dg χ ^ 2 ≤ p ^ 3 := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun χ' => dg χ' ^ 2)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ χ)
    rw [hdgk, ← pow_mul] at hle
    have h2k : k * 2 ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    have hk1 : k = 1 := by omega
    rw [hdgk, hk1, pow_one]
  -- the linear count `p²` and the nonlinear count `p − 1`
  have hLin : (Finset.univ.filter
      fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
        (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).card = p ^ 2 := by
    rw [card_filter_degree_one_eq_card_abelianization]
    exact card_abelianization_eq_prime_sq_of_card_eq_prime_cube hp hcard hnonab
  have hNL : (Finset.univ.filter
      fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
        ¬ (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).card = p - 1 := by
    have hLsum : ∑ χ ∈ Finset.univ.filter
        (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1), dg χ ^ 2
        = p ^ 2 := by
      rw [← hLin, Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [Finset.mem_filter] at hχ
      have hdg1 : dg χ = 1 := by
        have hcast : ((dg χ : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
          rw [← hdgeq χ, Nat.cast_one]
          exact hχ.2
        exact_mod_cast hcast
      rw [hdg1, one_pow]
    have hNsum : ∑ χ ∈ Finset.univ.filter
        (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          ¬ (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1), dg χ ^ 2
        = (Finset.univ.filter
          (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
            ¬ (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1)).card
          * p ^ 2 := by
      calc ∑ χ ∈ Finset.univ.filter
            (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
              ¬ (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1), dg χ ^ 2
          = ∑ _χ ∈ Finset.univ.filter
            (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
              ¬ (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1), p ^ 2 :=
            Finset.sum_congr rfl fun χ hχ => by
              rw [Finset.mem_filter] at hχ
              rw [hdg_nl χ hχ.2]
        _ = (Finset.univ.filter
            (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
              ¬ (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1)).card
            * p ^ 2 := by
            rw [Finset.sum_const, smul_eq_mul]
    have htotal := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
        (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1)
      (fun χ => dg χ ^ 2)
    rw [hsum, hLsum, hNsum] at htotal
    have h1 : (1 + (Finset.univ.filter
        (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          ¬ (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1)).card) * p ^ 2
        = p * p ^ 2 := by
      have hpp : p * p ^ 2 = p ^ 3 := by ring
      rw [add_mul, one_mul, hpp]
      exact htotal
    have h2 := Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) h1
    omega
  -- the reducible-inducing sources: exactly `w₂ = p` of them (the columns `χ_j`)
  have hRed : (Finset.univ.filter
      fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
        ¬ IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
          (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ))).card = p := by
    have hW2card : Nat.card ↥h.W2 = p := by
      rw [hpw2]
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (typePData_W2_le_self hyp.typeP)).toEquiv
    have hbij : Nat.card {χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) //
        ¬ IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
          (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ))} = p :=
      (h.card_reducible_induce_eq_W2).trans hW2card
    rw [← hbij, Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- the trivial character induces reducibly (the trivial column)
  have htrivRed : trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M)
      ∈ Finset.univ.filter
        (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          ¬ IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
            (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ))) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 := h.induce_chiRestrict_not_isIrreducible 1
    rwa [h.chiRestrict_one_eq_trivial] at h1
  -- nontrivial reducible-inducing sources are nonlinear (linear nontrivial ⟹ Ind irreducible)
  have hsub : (Finset.univ.filter
      fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
        ¬ IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
          (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ))).erase
        (trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M))
      ⊆ Finset.univ.filter
        (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          ¬ (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1) := by
    intro χ hχ
    rw [Finset.mem_erase] at hχ
    obtain ⟨hχne, hχRed⟩ := hχ
    rw [Finset.mem_filter] at hχRed ⊢
    refine ⟨Finset.mem_univ _, fun hlin => ?_⟩
    exact hχRed.2 (isIrreducibleCharacter_induce_of_inertia_eq χ
      (hyp.inertia_eq_derived_of_linear hG hχne hlin))
  -- equal counts `p − 1` force equality: every nonlinear source induces reducibly
  have heq : (Finset.univ.filter
      fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
        ¬ IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
          (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ))).erase
        (trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M))
      = Finset.univ.filter
        (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          ¬ (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1) := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hNL, Finset.card_erase_of_mem htrivRed, hRed]
  -- conclude: an irreducibly-inducing nontrivial `θ` cannot be nonlinear
  by_contra hlin
  have hθNL : θ ∈ Finset.univ.filter
      (fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
        ¬ (χ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hlin⟩
  rw [← heq, Finset.mem_erase, Finset.mem_filter] at hθNL
  exact hθNL.2.2 hirr

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.2), the structure of `S`** — the `hstruct` input of
`typeV_caseC_coherence_engine`: with `H = M′` non-abelian of order `p³` (`p = w₂`, case (c)
of Definition (8.7)), every member of `S = {Ind_{M′}^M θ | θ ≠ 1}` is either a degree-`w₁`
irreducible (a member of `S₁ = S(HC)`) or a nonzero μ-grid column sum
`μ_j = ∑_i μ_{ij}`.

Book: "`S = S₁ ∪ {μ_j | 0 < j < p}`".  Dichotomy on `φ = Ind_{M′}^M θ`:

* `φ` irreducible — the source is linear
  (`linear_of_induce_isIrreducible_of_card_eq_prime_cube`, the `p³` counting), so
  `φ(1) = [M : M′]·θ(1) = w₁` (`induce_apply_one` + `card_W1_eq_derived_index`) and
  `φ ∈ S(HC)`;
* `φ` reducible — the source is a certain-type column `χ_j` (`induce_not_isIrreducible_iff`)
  with `j ≠ 0` (`θ ≠ 1`, `chiRestrict_one_eq_trivial`), and `Ind_{M′}^M χ_j = μ_j`
  (`induce_restrict_certainType_eq`; the type-V clone of the type-III/IV
  `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum`, whose `htype`/`chief` inputs its
  proof never used). -/
theorem Hypothesis.mem_SHCSet_or_eq_muGrid_columnSum_of_card_eq_prime_cube [Finite G]
    {M : Subgroup G} (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {p : ℕ} (hp : p.Prime) (hpw2 : p = hyp.w2)
    (hcard : Nat.card ↥((derivedInG M).subgroupOf M) = p ^ 3)
    (hnonab : ¬ IsMulCommutative ↥((derivedInG M).subgroupOf M)) :
    ∀ φ ∈ hyp.Sset, φ ∈ hyp.SHCSet ∨
      ∃ j : Fin hyp.w2, j ≠ 0 ∧ φ = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j := by
  have := hyp.finiteG
  classical
  intro φ hφS
  have hφmem : φ ∈ inducedFamily M := hφS
  obtain ⟨θ, hθne, rfl⟩ := hφmem
  by_cases hirr : IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ))
  · -- irreducible: linear source, degree `w₁` — an `S₁ = S(HC)` member
    left
    have hθ1 : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1 :=
      hyp.linear_of_induce_isIrreducible_of_card_eq_prime_cube hG hodd hp hpw2 hcard hnonab
        hirr
    refine ⟨⟨θ, hθne, rfl⟩, hirr, ?_⟩
    have hidx : ((derivedInG M).subgroupOf M).index = hyp.w1 :=
      hyp.typeP.card_W1_eq_derived_index.symm
    rw [ClassFunction.induce_apply_one, hθ1, mul_one, hidx]
  · -- reducible: a nonzero μ-grid column sum (type-V clone of
    -- `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum`)
    right
    let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
    have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
    have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
    let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
    let : Fintype ↥M := Fintype.ofFinite _
    let : Fintype ↥h.K := Fintype.ofFinite _
    let : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
    have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
    have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
    have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
    have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
    have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
    have hFk : ∀ j : Fin hyp.w2, (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
        = ClassFunction.induce h.K
            ((h.chiRestrict (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)))
              : ClassFunction ↥h.K ℂ) := by
      intro j
      rw [h.coe_chiRestrict, h.induce_restrict_certainType_eq,
        ← Equiv.sum_comp (finCongr hcardW1.symm)
        (fun i' => ((h.columnFamily
          (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu i'
            : ClassFunction ↥M ℂ))]
      exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
    obtain ⟨χ₂', hχ₂'⟩ := (h.induce_not_isIrreducible_iff θ).mp hirr
    have hχ₂'ne : χ₂' ≠ 1 := by
      rintro rfl
      rw [h.chiRestrict_one_eq_trivial] at hχ₂'
      exact hθne hχ₂'.symm
    refine ⟨finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'), ?_, ?_⟩
    · intro h0
      apply hχ₂'ne
      have hs0 : (finCardEquivCharacterGroup
          ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))).symm χ₂' = 0 := by
        have := congrArg (finCongr hcardW2sub.symm) h0
        simpa using this
      calc χ₂' = finCardEquivCharacterGroup _
            ((finCardEquivCharacterGroup _).symm χ₂') := (Equiv.apply_symm_apply _ _).symm
        _ = finCardEquivCharacterGroup _ 0 := by rw [hs0]
        _ = 1 := finCardEquivCharacterGroup_zero _
    · rw [hFk, show finCongr hcardW2sub.symm
          (finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'))
          = (finCardEquivCharacterGroup _).symm χ₂' from by simp,
        Equiv.apply_symm_apply, hχ₂']
      exact rfl

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.2), the grid-degree identification `d = p`**: with `H = M′` of order
`p³`, the common nontrivial-column degree `d = μ_{ij}(1)` of the (10.3) grid equals `p`
(book: "In the notation of (10.3), `d = p`").

The column sum `μ_1 = ∑_i μ_{i1}` (the column `j = 1` exists since `w₂` is prime) lies in
`S = {Ind_{M′}^M θ | θ ≠ 1}` (`muGrid_column_sum_mem_inducedFamily`, using `d ≠ 1`), so its
degree computes two ways: `w₁·d` row-by-row (`hdeg`) and `[M : M′]·θ(1) = w₁·θ(1)` through
the induction (`induce_apply_one` + `card_W1_eq_derived_index`) — hence `θ(1) = d`.  As an
irreducible degree of the `p`-group `M′`, `d = p^k`
(`exists_natDegree_characterDegree_eq_prime_pow_of_isPGroup`) with
`d² ≤ ∑_{θ' ∈ Irr M′} θ'(1)² = |M′| = p³` (`sumIrreducibleDegreeSq`), so `2k ≤ 3`; and
`d > 1` ((10.3), `d_gt_one`) rules out `k = 0`, leaving `k = 1`, i.e. `d = p`.  This pins
the (10.10.1) arithmetic `p = 2w₁ − 1` onto the grid parameter `d` for the numeric inputs
(`delta_eq_neg_one` / `n_eq_two`) of `typeV_caseC_coherence_engine`. -/
theorem Hypothesis.muGrid_degree_eq_prime_of_card_eq_prime_cube [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card ↥((derivedInG M).subgroupOf M) = p ^ 3)
    {d : ℕ} (hd1 : 1 < d)
    (hdeg : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
      hyp.muGrid hG hodd i j 1 = (d : ℂ)) :
    d = p := by
  have := hyp.finiteG
  have : Fact p.Prime := ⟨hp⟩
  classical
  have hw2ge : 2 ≤ hyp.w2 := (hyp.w2_prime hG).two_le
  have hj : (⟨1, by omega⟩ : Fin hyp.w2) ≠ 0 := Fin.ne_of_val_ne (by simp)
  have h3 : (3 : ℕ) ≤ hyp.w1 :=
    (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  have hw1C : (hyp.w1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- `μ_1 = Ind_{M′}^M θ` for a (nontrivial) irreducible `θ` of `M′`
  have hμS : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (⟨1, by omega⟩ : Fin hyp.w2))
      ∈ inducedFamily M := by
    refine hyp.muGrid_column_sum_mem_inducedFamily hG hodd _ ?_
    rw [hdeg 0 _ hj]
    intro hone
    have hd' : d = 1 := by exact_mod_cast hone
    omega
  obtain ⟨θ, -, hθeq⟩ := hμS
  -- degree of the column, row-by-row: `w₁·d`
  have hcol : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (⟨1, by omega⟩ : Fin hyp.w2)) 1
      = (hyp.w1 : ℂ) * (d : ℂ) := by
    rw [ClassFunction.finset_sum_apply, Finset.sum_congr rfl (fun i _ => hdeg i _ hj),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- `θ(1) = p^k` with a natural witness `e`
  have hpg : IsPGroup p ↥((derivedInG M).subgroupOf M) := IsPGroup.of_card hcard
  obtain ⟨e, k, hepos, hedeg, hepk⟩ :=
    OddOrder.Peterfalvi.S03.exists_natDegree_characterDegree_eq_prime_pow_of_isPGroup hpg θ
  rw [OddOrder.Peterfalvi.S03.characterDegree_def] at hedeg
  -- degree of the column, through the induction: `w₁·e`
  have hidx : ((derivedInG M).subgroupOf M).index = hyp.w1 :=
    hyp.typeP.card_W1_eq_derived_index.symm
  have hind : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i (⟨1, by omega⟩ : Fin hyp.w2)) 1
      = (hyp.w1 : ℂ) * (e : ℂ) := by
    rw [hθeq, ClassFunction.induce_apply_one, hidx, hedeg]
  -- cancel `w₁`: `d = e`
  have hde : d = e := by
    have hC : (hyp.w1 : ℂ) * (d : ℂ) = (hyp.w1 : ℂ) * (e : ℂ) := by rw [← hcol, hind]
    exact_mod_cast mul_left_cancel₀ hw1C hC
  -- Burnside bound: `e² ≤ ∑ θ'(1)² = p³`
  choose dg dgpos hdgeq using fun χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
    irreducibleCharacter_apply_one_eq_pos_natCast χ
  have hsumC := OddOrder.RepresentationTheory.sumIrreducibleDegreeSq
    (G := ↥((derivedInG M).subgroupOf M))
  rw [hcard] at hsumC
  have hsum : ∑ χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M), dg χ ^ 2
      = p ^ 3 := by
    have hC : ((∑ χ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M), dg χ ^ 2 : ℕ) : ℂ)
        = ((p ^ 3 : ℕ) : ℂ) := by
      rw [Nat.cast_sum, ← hsumC]
      exact Finset.sum_congr rfl fun χ _ => by rw [Nat.cast_pow, hdgeq χ]
    exact_mod_cast hC
  have hdgθ : dg θ = e := by
    have hC : ((dg θ : ℕ) : ℂ) = ((e : ℕ) : ℂ) := by rw [← hdgeq θ, hedeg]
    exact_mod_cast hC
  have hle : e ^ 2 ≤ p ^ 3 := by
    rw [← hdgθ, ← hsum]
    exact Finset.single_le_sum (f := fun χ' => dg χ' ^ 2) (fun i _ => Nat.zero_le _)
      (Finset.mem_univ θ)
  -- `2k ≤ 3` and `k ≠ 0` force `k = 1`
  rw [hepk, ← pow_mul] at hle
  have h2k : k * 2 ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hepk
    omega
  have hk1 : k = 1 := by omega
  rw [hde, hepk, hk1, pow_one]

end OddOrder.Peterfalvi.S12


