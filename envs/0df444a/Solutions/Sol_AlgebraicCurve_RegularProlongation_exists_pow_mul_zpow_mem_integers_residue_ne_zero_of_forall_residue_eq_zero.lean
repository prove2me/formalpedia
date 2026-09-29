-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ad9e78c6-8a62-5700-b6af-b3a20297c2c9

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_ValuationSubring_exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero

set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing

noncomputable section

namespace OneSidedWitnessExponent

private theorem eq_one_of_pow_eq_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a : Γ₀} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : a = 1 := by
  have hle1 : ∀ m : ℕ, a ≤ 1 → a ^ m ≤ 1 := fun m ha => by
    induction m with
    | zero => rw [pow_zero]
    | succ m ih =>
      rw [pow_succ]
      calc a ^ m * a ≤ 1 * 1 := mul_le_mul' ih ha
        _ = 1 := one_mul 1
  have hge1 : ∀ m : ℕ, 1 ≤ a → 1 ≤ a ^ m := fun m ha => by
    induction m with
    | zero => rw [pow_zero]
    | succ m ih =>
      rw [pow_succ]
      calc (1 : Γ₀) = 1 * 1 := (one_mul 1).symm
        _ ≤ a ^ m * a := mul_le_mul' ih ha
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rcases lt_trichotomy a 1 with ha | ha | ha
  · exfalso
    have hle : a ^ (m + 1) ≤ a := by
      rw [pow_succ]
      calc a ^ m * a ≤ 1 * a := mul_le_mul' (hle1 m ha.le) le_rfl
        _ = a := one_mul a
    rw [h] at hle
    exact absurd (lt_of_le_of_lt hle ha) (lt_irrefl 1)
  · exact ha
  · exfalso
    have hle : a ≤ a ^ (m + 1) := by
      rw [pow_succ]
      calc a = 1 * a := (one_mul a).symm
        _ ≤ a ^ m * a := mul_le_mul' (hge1 m ha.le) le_rfl
    rw [h] at hle
    exact absurd (lt_of_lt_of_le ha hle) (lt_irrefl 1)

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem mem_decompositionSubgroup_of_mem_inertiaSubgroupIn
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    σ ∈ A.decompositionSubgroup ℚ := by
  unfold ValuationSubring.inertiaSubgroupIn at hσ
  exact Subgroup.map_subtype_le _ hσ

private theorem valuation_map_eq_of_mem_inertiaSubgroupIn
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (z : AlgebraicClosure ℚ) : A.valuation (σ z) = A.valuation z :=
  ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A
    (mem_decompositionSubgroup_of_mem_inertiaSubgroupIn A hσ) z

private theorem exists_inertia_fixed_valuation_eq_pow (x : AlgebraicClosure ℚ) (hx : x ≠ 0) :
    ∃ (e : ℕ) (y : AlgebraicClosure ℚ), e ≠ 0 ∧ y ≠ 0 ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ → σ y = y) ∧
      A.valuation y = A.valuation x ^ e := by
  classical

  set O : Set (AlgebraicClosure ℚ) :=
    {z | ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ ∧ σ x = z}
    with hO_def
  have hint : IsIntegral ℚ x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hroot : Polynomial.aeval x (minpoly ℚ x) = 0 := minpoly.aeval ℚ x
  have hsub : O ⊆ (minpoly ℚ x).rootSet (AlgebraicClosure ℚ) := by
    rintro z ⟨σ, -, rfl⟩
    refine Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, hroot, map_zero]
  have hfin : O.Finite := (Polynomial.rootSet_finite _ _).subset hsub
  have hmemS : ∀ z, z ∈ hfin.toFinset ↔ ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ∧ σ x = z := fun z => by
    rw [Set.Finite.mem_toFinset]
    rfl
  have hxS : x ∈ hfin.toFinset := (hmemS x).mpr ⟨1, Subgroup.one_mem _, rfl⟩

  have himage : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ A.inertiaSubgroupIn ℚ →
      hfin.toFinset.image τ = hfin.toFinset := fun τ hτ => by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨σ, hσ, rfl⟩ := (hmemS w).mp hw
      exact (hmemS _).mpr ⟨τ * σ, Subgroup.mul_mem _ hτ hσ, rfl⟩
    · exact (Finset.card_image_of_injective _ τ.injective).ge
  refine ⟨hfin.toFinset.card, ∏ z ∈ hfin.toFinset, z, ?_, ?_, ?_, ?_⟩
  · exact Finset.card_ne_zero.mpr ⟨x, hxS⟩
  · rw [Finset.prod_ne_zero_iff]
    intro z hz
    obtain ⟨σ, -, rfl⟩ := (hmemS z).mp hz
    exact (map_ne_zero σ).mpr hx
  · intro τ hτ
    rw [map_prod]
    have hinj : ∀ a ∈ hfin.toFinset, ∀ b ∈ hfin.toFinset, τ a = τ b → a = b :=
      fun a _ b _ h => τ.injective h
    have himg := Finset.prod_image (f := fun z : AlgebraicClosure ℚ => z) hinj
    rw [himage τ hτ] at himg
    exact himg.symm
  · rw [map_prod]
    have hconst : ∀ z ∈ hfin.toFinset, A.valuation z = A.valuation x := fun z hz => by
      obtain ⟨σ, hσ, rfl⟩ := (hmemS z).mp hz
      exact valuation_map_eq_of_mem_inertiaSubgroupIn A hσ x
    rw [Finset.prod_congr rfl hconst, Finset.prod_const]

variable {A}

private theorem valuation_eq_one_of_mem_of_inv_mem {u : AlgebraicClosure ℚ} (hu0 : u ≠ 0)
    (hu : u ∈ A) (hu' : u⁻¹ ∈ A) : A.valuation u = 1 := by
  have h1 : A.valuation u ≤ 1 := (A.valuation_le_one_iff u).mpr hu
  have h2 : A.valuation u⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hu'
  by_contra hne
  have hlt : A.valuation u < 1 := lt_of_le_of_ne h1 hne
  have hprod : A.valuation u * A.valuation u⁻¹ < 1 :=
    calc A.valuation u * A.valuation u⁻¹ ≤ A.valuation u * 1 := mul_le_mul' le_rfl h2
      _ = A.valuation u := mul_one _
      _ < 1 := hlt
  rw [← map_mul, mul_inv_cancel₀ hu0, map_one] at hprod
  exact lt_irrefl _ hprod

private theorem exists_valuation_eq_zpow_of_inertia_fixed {q : ℕ} [Fact q.Prime]
    (hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (y : AlgebraicClosure ℚ) (hy : y ≠ 0)
    (hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ → σ y = y) :
    ∃ s : ℤ, A.valuation y = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ s := by
  rcases A.mem_or_inv_mem y with hyA | hyA
  · obtain ⟨s, u, huA, hu'A, hyeq⟩ :=
      ValuationSubring.exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn q A hA y hyA hy hfix
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hyeq
      exact hy hyeq
    refine ⟨s, ?_⟩
    rw [hyeq, map_mul, map_pow, valuation_eq_one_of_mem_of_inv_mem hu0 huA hu'A, mul_one,
      zpow_natCast]
  · have hy' : y⁻¹ ≠ 0 := inv_ne_zero hy
    have hfix' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        σ ∈ A.inertiaSubgroupIn ℚ → σ y⁻¹ = y⁻¹ := fun σ hσ => by
      rw [map_inv₀, hfix σ hσ]
    obtain ⟨s, u, huA, hu'A, hyeq⟩ :=
      ValuationSubring.exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn q A hA y⁻¹ hyA hy' hfix'
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hyeq
      exact hy' hyeq
    refine ⟨-(s : ℤ), ?_⟩
    have hv : A.valuation y⁻¹ = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ s := by
      rw [hyeq, map_mul, map_pow, valuation_eq_one_of_mem_of_inv_mem hu0 huA hu'A, mul_one]
    rw [map_inv₀] at hv
    rw [zpow_neg, zpow_natCast, ← hv, inv_inv]

private theorem exists_pow_mul_zpow_valuation_eq_one {q : ℕ} [Fact q.Prime]
    (hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (c d : AlgebraicClosure ℚ) (hc : c ≠ 0) (hd : d ≠ 0) (hd1 : A.valuation d ≠ 1) :
    ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧ A.valuation (c ^ m * d ^ j) = 1 := by
  set V := A.valuation ((q : ℕ) : AlgebraicClosure ℚ) with hV_def
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hV0 : V ≠ 0 := (map_ne_zero _).mpr hq0
  obtain ⟨ec, yc, hec, hyc, hfixc, hvc⟩ := exists_inertia_fixed_valuation_eq_pow A c hc
  obtain ⟨ed, yd, hed, hyd, hfixd, hvd⟩ := exists_inertia_fixed_valuation_eq_pow A d hd
  obtain ⟨sc, hsc⟩ := exists_valuation_eq_zpow_of_inertia_fixed hA yc hyc hfixc
  obtain ⟨sd, hsd⟩ := exists_valuation_eq_zpow_of_inertia_fixed hA yd hyd hfixd

  have hc' : A.valuation c ^ (ec : ℤ) = V ^ sc := by rw [zpow_natCast, ← hvc, hsc]
  have hd' : A.valuation d ^ (ed : ℤ) = V ^ sd := by rw [zpow_natCast, ← hvd, hsd]

  have hsd0 : sd ≠ 0 := by
    rintro rfl
    rw [zpow_zero, zpow_natCast] at hd'
    exact hd1 (eq_one_of_pow_eq_one hed hd')
  rcases lt_or_gt_of_ne hsd0 with hneg | hpos
  ·
    refine ⟨ec * sd.natAbs, (ed : ℤ) * sc, ?_, ?_⟩
    · exact Nat.mul_ne_zero hec (Int.natAbs_ne_zero.mpr hsd0)
    have habs : ((sd.natAbs : ℕ) : ℤ) = -sd := Int.ofNat_natAbs_of_nonpos hneg.le
    rw [map_mul, map_zpow₀, map_pow, ← zpow_natCast, Nat.cast_mul, habs, zpow_mul, hc',
      zpow_mul, hd', ← zpow_mul, ← zpow_mul, ← zpow_add₀ hV0]
    have : sc * -sd + sd * sc = 0 := by ring
    rw [this, zpow_zero]
  ·
    refine ⟨ec * sd.natAbs, -((ed : ℤ) * sc), ?_, ?_⟩
    · exact Nat.mul_ne_zero hec (Int.natAbs_ne_zero.mpr hsd0)
    have habs : ((sd.natAbs : ℕ) : ℤ) = sd := Int.natAbs_of_nonneg hpos.le
    rw [map_mul, map_zpow₀, map_pow, ← zpow_natCast, Nat.cast_mul, habs, zpow_mul, hc',
      zpow_neg, zpow_mul, hd', ← zpow_mul, ← zpow_neg, ← zpow_mul, ← zpow_add₀ hV0]
    have : sc * sd + sd * -sc = 0 := by ring
    rw [this, zpow_zero]

private theorem exists_prime_mem_nonunits_or_forall_valuation_eq_one :
    (∃ q : ℕ, q.Prime ∧ ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) ∨
      ∀ x : AlgebraicClosure ℚ, x ≠ 0 → A.valuation x = 1 := by
  classical
  by_cases h : ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
  · exact Or.inl h
  refine Or.inr ?_
  push Not at h

  have hnat : ∀ n : ℕ, n ≠ 0 → A.valuation ((n : ℕ) : AlgebraicClosure ℚ) = 1 := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h0; exact absurd rfl h0
    | one => intro; simp
    | prime p hp =>
      intro
      have hle : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (natCast_mem A p)
      have hnlt : ¬ A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := by
        rw [← ValuationSubring.mem_nonunits_iff]
        exact h p hp
      exact le_antisymm hle (not_lt.mp hnlt)
    | mul a b ha hb =>
      intro hab
      rw [Nat.cast_mul, map_mul, ha (left_ne_zero_of_mul hab), hb (right_ne_zero_of_mul hab), one_mul]

  have hint' : ∀ z : ℤ, z ≠ 0 → A.valuation ((z : ℤ) : AlgebraicClosure ℚ) = 1 := by
    intro z hz
    obtain ⟨n, hn | hn⟩ := z.eq_nat_or_neg
    · rw [hn, Int.cast_natCast]
      exact hnat n (by rintro rfl; exact hz (by rw [hn]; rfl))
    · rw [hn, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]
      exact hnat n (by rintro rfl; exact hz (by rw [hn]; rfl))
  have hrat : ∀ r : ℚ, r ≠ 0 → A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) r) = 1 := by
    intro r hr
    have hnum : A.valuation ((r.num : ℤ) : AlgebraicClosure ℚ) = 1 := hint' r.num (Rat.num_ne_zero.mpr hr)
    have hden : A.valuation ((r.den : ℕ) : AlgebraicClosure ℚ) = 1 := hnat r.den r.den_ne_zero
    have hr' : algebraMap ℚ (AlgebraicClosure ℚ) r * ((r.den : ℕ) : AlgebraicClosure ℚ) = ((r.num : ℤ) : AlgebraicClosure ℚ) := by
      rw [← map_natCast (algebraMap ℚ (AlgebraicClosure ℚ)), ← map_intCast (algebraMap ℚ (AlgebraicClosure ℚ)), ← map_mul,
        Rat.mul_den_eq_num]
    have h := congrArg A.valuation hr'
    rw [map_mul, hden, mul_one, hnum] at h
    exact h

  have hle : ∀ x : AlgebraicClosure ℚ, A.valuation x ≤ 1 := by
    intro x
    by_contra hx
    rw [not_le] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact not_lt_zero hx
    have hint : IsIntegral ℚ x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hmonic : (minpoly ℚ x).Monic := minpoly.monic hint
    have heval : x ^ (minpoly ℚ x).natDegree =
        -∑ i ∈ Finset.range (minpoly ℚ x).natDegree, algebraMap ℚ (AlgebraicClosure ℚ) ((minpoly ℚ x).coeff i) * x ^ i := by
      have h0 : Polynomial.aeval x (minpoly ℚ x) = 0 := minpoly.aeval ℚ x
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, one_smul] at h0
      rw [eq_neg_iff_add_eq_zero, add_comm]
      simpa only [Algebra.smul_def] using h0
    have hlt : A.valuation (∑ i ∈ Finset.range (minpoly ℚ x).natDegree,
        algebraMap ℚ (AlgebraicClosure ℚ) ((minpoly ℚ x).coeff i) * x ^ i) < A.valuation x ^ (minpoly ℚ x).natDegree := by
      refine Valuation.map_sum_lt _ (pow_ne_zero _ ((map_ne_zero _).mpr hx0)) fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [map_mul, map_pow]
      have hc : A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) ((minpoly ℚ x).coeff i)) ≤ 1 := by
        by_cases hci : (minpoly ℚ x).coeff i = 0
        · rw [hci, map_zero, map_zero]; exact zero_le'
        · exact (hrat _ hci).le
      calc A.valuation (algebraMap ℚ (AlgebraicClosure ℚ) ((minpoly ℚ x).coeff i)) * A.valuation x ^ i
          ≤ 1 * A.valuation x ^ i := mul_le_mul' hc le_rfl
        _ = A.valuation x ^ i := one_mul _
        _ < A.valuation x ^ (minpoly ℚ x).natDegree := pow_lt_pow_right₀ hx hi
    rw [← map_pow, heval, Valuation.map_neg] at hlt
    exact lt_irrefl _ hlt
  intro x hx0
  exact valuation_eq_one_of_mem_of_inv_mem hx0 ((A.valuation_le_one_iff _).mp (hle x))
    ((A.valuation_le_one_iff _).mp (hle x⁻¹))

end OneSidedWitnessExponent

end

set_option maxHeartbeats 3200000 in
open AlgebraicCurve IsLocalRing OneSidedWitnessExponent in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (F : Type*) [Field F] [Algebra (AlgebraicClosure ℚ) F]
    (Fbar : Type*) [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (u : F) (hu0 : u ≠ 0) (hu : ∀ h : u ∈ R.integers, R.residue ⟨u, h⟩ = 0)
    (f : F) (hf : f ≠ 0) :
    ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧ ∃ h : f ^ m * u ^ j ∈ R.integers, R.residue ⟨f ^ m * u ^ j, h⟩ ≠ 0 := by

  have hres_const : ∀ (a : AlgebraicClosure ℚ) (haA : a ∈ A), A.valuation a = 1 →
      ∀ hmem : algebraMap (AlgebraicClosure ℚ) F a ∈ R.integers,
        R.residue ⟨_, hmem⟩ ≠ 0 := fun a haA hva hmem => by
    have key : R.residue ⟨_, hmem⟩ =
        algebraMap (ResidueField A) Fbar
          (IsLocalRing.residue A ⟨a, haA⟩) := R.residue_algebraMap ⟨a, haA⟩
    have hunit : IsUnit (⟨a, haA⟩ : A) := by
      rw [A.valuation_eq_one_iff]
      exact hva
    intro h0
    rw [key, map_eq_zero_iff _ (algebraMap (ResidueField A)
      Fbar).injective,
      IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h0
    exact h0 hunit

  obtain ⟨cu, hcu, hcures⟩ := R.exists_smul_mem u hu0
  have hcu0 : cu ≠ 0 := R.smul_const_ne_zero hcu hcures
  have hcu1 : A.valuation cu ≠ 1 := by
    intro h1
    have hvinv : A.valuation cu⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
    have hcu'A : cu⁻¹ ∈ A := (A.valuation_le_one_iff _).mp hvinv.le
    have hconst : algebraMap (AlgebraicClosure ℚ) F cu⁻¹ ∈ R.integers := (R.algebraMap_mem_iff _).mpr hcu'A
    have hueq : u = algebraMap (AlgebraicClosure ℚ) F cu⁻¹ * (cu • u) := by
      rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hcu0, map_one, one_mul]
    have h₂ : u ∈ R.integers := by
      rw [hueq]
      exact mul_mem hconst hcu
    have hprod : (⟨u, h₂⟩ : R.integers) = ⟨_, hconst⟩ * ⟨cu • u, hcu⟩ := Subtype.ext hueq
    have hne : R.residue ⟨u, h₂⟩ ≠ 0 := by
      rw [hprod, map_mul]
      exact mul_ne_zero (hres_const cu⁻¹ hcu'A hvinv hconst) hcures
    exact hne (hu h₂)

  obtain ⟨q, hq, hA⟩ : ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
    rcases exists_prime_mem_nonunits_or_forall_valuation_eq_one (A := A) with h | h
    · exact h
    · exact absurd (h cu hcu0) hcu1
  haveI : Fact q.Prime := ⟨hq⟩

  obtain ⟨cf, hcf, hcfres⟩ := R.exists_smul_mem f hf
  have hcf0 : cf ≠ 0 := R.smul_const_ne_zero hcf hcfres

  obtain ⟨m, j, hm, hval⟩ := exists_pow_mul_zpow_valuation_eq_one hA cf cu hcf0 hcu0 hcu1
  set e : AlgebraicClosure ℚ := cf ^ m * cu ^ j with he_def
  have he0 : e ≠ 0 := mul_ne_zero (pow_ne_zero _ hcf0) (zpow_ne_zero _ hcu0)
  have heA : e ∈ A := (A.valuation_le_one_iff _).mp hval.le
  have hvinv : A.valuation e⁻¹ = 1 := by rw [map_inv₀, hval, inv_one]
  have he'A : e⁻¹ ∈ A := (A.valuation_le_one_iff _).mp hvinv.le

  set wu : (R.integers)ˣ := (R.isUnit_of_residue_ne_zero hcures).unit with hwu_def
  have hwu_val : ((wu : R.integers) : F) = cu • u := by
    rw [hwu_def, IsUnit.unit_spec]
  have hzpow : ((((wu ^ j : (R.integers)ˣ) : R.integers) : F))
      = (cu • u) ^ j := by
    have := congrArg
      (fun x : Fˣ => (x : F))
      (map_zpow (Units.map (R.integers.subtype : R.integers →* F))
        wu j)
    simp only [Units.coe_map, Units.val_zpow_eq_zpow_val] at this
    rw [← hwu_val]
    exact this
  have hmem_pow : (cf • f) ^ m ∈ R.integers := pow_mem hcf m
  have hmem_zpow : (cu • u) ^ j ∈ R.integers := by
    rw [← hzpow]
    exact ((wu ^ j : (R.integers)ˣ) : R.integers).2
  have hconst' : algebraMap (AlgebraicClosure ℚ) F e⁻¹
      ∈ R.integers := (R.algebraMap_mem_iff _).mpr he'A

  have hφ0 : algebraMap (AlgebraicClosure ℚ) F e ≠ 0 :=
    (map_ne_zero _).mpr he0
  have hid0 : algebraMap (AlgebraicClosure ℚ) F e * (f ^ m * u ^ j)
      = (cf • f) ^ m * (cu • u) ^ j := by
    rw [he_def, Algebra.smul_def, Algebra.smul_def, mul_pow, mul_zpow, map_mul, map_pow, map_zpow₀]
    ring
  have hid : f ^ m * u ^ j =
      algebraMap (AlgebraicClosure ℚ) F e⁻¹ *
        ((cf • f) ^ m * (cu • u) ^ j) := by
    rw [map_inv₀]
    exact (eq_inv_mul_iff_mul_eq₀ hφ0).mpr hid0
  have hmem : f ^ m * u ^ j ∈ R.integers := by
    rw [hid]
    exact mul_mem hconst' (mul_mem hmem_pow hmem_zpow)
  refine ⟨m, j, hm, hmem, ?_⟩

  have hres_pow : R.residue ⟨(cf • f) ^ m, hmem_pow⟩ ≠ 0 := by
    have hpow : (⟨(cf • f) ^ m, hmem_pow⟩ : R.integers) = (⟨cf • f, hcf⟩ : R.integers) ^ m :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow])
    rw [hpow, map_pow]
    exact pow_ne_zero _ hcfres
  have hres_zpow : R.residue ⟨(cu • u) ^ j, hmem_zpow⟩ ≠ 0 := by
    have hzp : (⟨(cu • u) ^ j, hmem_zpow⟩ : R.integers) =
        ((wu ^ j : (R.integers)ˣ) : R.integers) := Subtype.ext hzpow.symm
    rw [hzp]
    exact R.residue_ne_zero_of_isUnit (Units.isUnit _)
  have hsplit : (⟨f ^ m * u ^ j, hmem⟩ : R.integers) =
      ⟨_, hconst'⟩ * (⟨(cf • f) ^ m, hmem_pow⟩ * ⟨(cu • u) ^ j, hmem_zpow⟩) :=
    Subtype.ext hid
  rw [hsplit, map_mul, map_mul]
  exact mul_ne_zero (hres_const e⁻¹ he'A hvinv hconst') (mul_ne_zero hres_pow hres_zpow)

end S_AlgebraicCurve_RegularProlongation_exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero (solution)
