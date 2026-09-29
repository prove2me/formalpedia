-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/92b79d31-f1bd-5444-bc68-11b166b16427

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq
import Theorems.Thm_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul
import Theorems.Thm_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv
import Theorems.Thm_ValuationSubring_exists_mul_pow_inv_mem_of_finiteDimensional_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq

open Polynomial AlgebraicCurve IsLocalRing

namespace H1Sol

variable {L : Type*} [Field L] (A : ValuationSubring L)

def IsGoodAt (d : ℕ) (t : L[X]) : Prop :=
  A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1

theorem IsGoodAt.valuation_le {d : ℕ} {t : L[X]} (ht : IsGoodAt A d t) (j : ℕ) :
    A.valuation (t.coeff j) ≤ 1 := by
  by_cases hj : j = d
  · rw [hj, ht.1]
  · exact (ht.2 j hj).le

theorem IsGoodAt.coeff_mem {d : ℕ} {t : L[X]} (ht : IsGoodAt A d t) (j : ℕ) : t.coeff j ∈ A :=
  (A.valuation_le_one_iff _).mp (ht.valuation_le A j)

theorem IsGoodAt.ne_zero {d : ℕ} {t : L[X]} (ht : IsGoodAt A d t) : t ≠ 0 := by
  intro h
  have := ht.1
  rw [h, coeff_zero, map_zero] at this
  exact zero_ne_one this

theorem IsGoodAt.mul_zero_good {d : ℕ} {t s : L[X]} (ht : IsGoodAt A d t) (hs : IsGoodAt A 0 s) :
    IsGoodAt A d (t * s) := by
  classical
  refine ⟨?_, fun j hj => ?_⟩
  · rw [coeff_mul, ← Finset.add_sum_erase _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_zero d) :
      (d, 0) ∈ Finset.HasAntidiagonal.antidiagonal d)]
    have hmain : A.valuation (t.coeff d * s.coeff 0) = 1 := by rw [map_mul, ht.1, hs.1, one_mul]
    have hrest : A.valuation (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal d).erase (d, 0), t.coeff x.1 * s.coeff x.2) < 1 := by
      apply Valuation.map_sum_lt _ one_ne_zero
      intro x hx
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [map_mul]
      have h2 : x.2 ≠ 0 := by
        intro h0
        apply hx.1
        ext
        · simpa [h0] using hx.2
        · exact h0
      calc A.valuation (t.coeff x.1) * A.valuation (s.coeff x.2)
          ≤ 1 * A.valuation (s.coeff x.2) := by gcongr; exact ht.valuation_le A _
        _ < 1 := by rw [one_mul]; exact hs.2 _ h2
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [hmain]; exact hrest), hmain]
  · rw [coeff_mul]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [map_mul]
    by_cases h1 : x.1 = d
    · have h2 : x.2 ≠ 0 := by omega
      calc A.valuation (t.coeff x.1) * A.valuation (s.coeff x.2)
          ≤ 1 * A.valuation (s.coeff x.2) := by gcongr; exact ht.valuation_le A _
        _ < 1 := by rw [one_mul]; exact hs.2 _ h2
    · calc A.valuation (t.coeff x.1) * A.valuation (s.coeff x.2)
          ≤ A.valuation (t.coeff x.1) * 1 := by gcongr; exact hs.valuation_le A _
        _ < 1 := by rw [mul_one]; exact ht.2 _ h1

variable {F : Type*} [Field F] [Algebra L F]

theorem aeval_ne_zero_of_isGoodAt {g : F} (hg : Transcendental L g) {d : ℕ} {t : L[X]}
    (ht : IsGoodAt A d t) : aeval g t ≠ 0 := fun h =>
  ht.ne_zero A (transcendental_iff.mp hg _ h)

def IsLam (f x : F) : Prop :=
  ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
    (∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1) ∧
    x * aeval f t = aeval f p

def IsLamPlus (g x : F) : Prop :=
  ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
    (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
    x * aeval g t = aeval g p

theorem IsLam.mul_isLamPlus {f x y : F} (hx : IsLam A f x) (hy : IsLamPlus A f y) :
    IsLam A f (x * y) := by
  obtain ⟨p, t, hp, ⟨d, hd⟩, hxe⟩ := hx
  obtain ⟨q, s, hq, hs, hye⟩ := hy
  refine ⟨p * q, t * s, fun j => ?_, ⟨d, IsGoodAt.mul_zero_good A hd hs⟩, ?_⟩
  · rw [coeff_mul]; exact sum_mem fun x _ => mul_mem (hp _) (hq _)
  · simp only [map_mul]
    linear_combination (y * aeval f s) * hxe + (aeval f p) * hye

end H1Sol

namespace H1Sol

section Main

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

theorem main (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers) (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ (z : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F) (m₀ : ℕ),
      (∀ σ i, z σ ∈ (R i).integers) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
        (f⁻¹) ^ m₀ * z σ ∈ V) ∧
      ∀ (x s : F), IsLam A f x → (∀ i, s ∈ (R i).integers) →
        (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → s ∈ V) →
        ∃ (lp lm : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F)
          (a : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → Fin m₀ → L),
          (∀ σ, IsLamPlus A f (lp σ)) ∧ (∀ σ, IsLamPlus A f⁻¹ (lm σ)) ∧ (∀ σ k, a σ k ∈ A) ∧
          x * s = ∑ σ, lp σ * z σ + ∑ σ, lm σ * ((f⁻¹) ^ m₀ * z σ) +
            ∑ σ, ∑ k : Fin m₀, algebraMap L F (a σ k) * ((f⁻¹) ^ (k : ℕ) * z σ) := by
  classical
  haveI := hfd

  obtain ⟨z, hzO, hzT, hzind, hB, hres⟩ :=
    AlgebraicCurve.RegularProlongation.exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq
      A Fb R hR f hf htrL hfd htr heq

  have hm : ∀ σ, ∃ m : ℕ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∉ V →
      z σ * (f ^ m)⁻¹ ∈ V := fun σ =>
    ValuationSubring.exists_mul_pow_inv_mem_of_finiteDimensional_adjoin f (z σ) (hzT σ)
  choose m hmV using hm
  set m₀ : ℕ := Finset.univ.sup m + 1 with hm₀
  have hmle : ∀ σ, m σ ≤ m₀ := fun σ =>
    (Finset.le_sup (f := m) (Finset.mem_univ σ)).trans (Nat.le_succ _)
  have hzT' : ∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
      (f⁻¹) ^ m₀ * z σ ∈ V := by
    intro σ V hV hfV
    by_cases hfV' : f ∈ V
    · exact mul_mem (pow_mem hfV _) (hzT σ V hV hfV')
    · have h := hmV σ V hV hfV'
      have heq' : (f⁻¹) ^ m₀ * z σ = (f⁻¹) ^ (m₀ - m σ) * (z σ * (f ^ m σ)⁻¹) := by
        have hpow : (f⁻¹) ^ m₀ = (f⁻¹) ^ (m₀ - m σ) * (f ^ m σ)⁻¹ := by
          rw [← inv_pow, ← pow_add, Nat.sub_add_cancel (hmle σ)]
        rw [hpow]; ring
      rw [heq']
      exact mul_mem (pow_mem hfV _) h
  refine ⟨z, m₀, hzO, hzT, hzT', ?_⟩

  intro x s hx hsO hsT
  obtain ⟨w, hw, hsw⟩ := hB s hsO

  have hwplus : ∀ σ, IsLamPlus A f (w σ) := by
    intro σ
    obtain ⟨p, t, hp, ht, hwe⟩ :=
      ValuationSubring.exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul A htrL z hzT hzind
        hres s w hsT hw hsw σ
    refine ⟨p, t, hp, ht, ?_⟩
    rw [hwe, div_mul_cancel₀ _ (aeval_ne_zero_of_isGoodAt A htrL (d := 0) ht)]

  have hsplit : ∀ σ, ∃ (lp lm : F) (a : Fin m₀ → L), IsLamPlus A f lp ∧ IsLamPlus A f⁻¹ lm ∧
      (∀ k, a k ∈ A) ∧
      x * w σ = lp + lm * (f⁻¹) ^ m₀ + ∑ k : Fin m₀, algebraMap L F (a k) * (f⁻¹) ^ (k : ℕ) := by
    intro σ
    obtain ⟨p, t, hp, ⟨d, hd⟩, hxe⟩ := hx.mul_isLamPlus A (hwplus σ)
    obtain ⟨p₁, t₁, q, s', r, hp₁, hq, hr, hrdeg, ht₁, hs', hdec⟩ :=
      ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv A htrL p t hp
        ⟨d, hd⟩ m₀
    have htrinv : Transcendental L f⁻¹ := fun h => htrL (IsAlgebraic.inv_iff.mp h)
    have ht0 : aeval f t ≠ 0 := aeval_ne_zero_of_isGoodAt A htrL hd
    have ht₁0 : aeval f t₁ ≠ 0 := aeval_ne_zero_of_isGoodAt A htrL (d := 0) ht₁
    have hs'0 : aeval f⁻¹ s' ≠ 0 := aeval_ne_zero_of_isGoodAt A htrinv (d := 0) hs'
    have hxw : x * w σ = aeval f p / aeval f t := by
      rw [← hxe, mul_div_cancel_right₀ _ ht0]
    have hrnat : r.natDegree < m₀ := by
      by_cases hr0 : r = 0
      · rw [hr0, natDegree_zero, hm₀]; exact Nat.succ_pos _
      · exact (natDegree_lt_iff_degree_lt hr0).mpr hrdeg
    refine ⟨aeval f p₁ / aeval f t₁, aeval f⁻¹ q / aeval f⁻¹ s', fun k => r.coeff k,
      ⟨p₁, t₁, hp₁, ht₁, div_mul_cancel₀ _ ht₁0⟩, ⟨q, s', hq, hs', div_mul_cancel₀ _ hs'0⟩,
      fun k => hr k, ?_⟩
    rw [hxw, hdec, aeval_eq_sum_range' hrnat, Finset.sum_range]
    simp only [Algebra.smul_def]
    ring
  choose lp lm a hlp hlm ha hsplitσ using hsplit
  refine ⟨lp, lm, a, hlp, hlm, ha, ?_⟩
  rw [hsw, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, hsplitσ σ, add_mul, add_mul, Finset.sum_mul]
  refine congrArg₂ _ (congrArg₂ _ rfl (by ring)) (Finset.sum_congr rfl fun k _ => by ring)

end Main

end H1Sol

open AlgebraicCurve in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ (z : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F) (m₀ : ℕ),
      (∀ σ i, z σ ∈ (R i).integers) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
        (f⁻¹) ^ m₀ * z σ ∈ V) ∧
      ∀ (x s : F),
        (∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
          (∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1) ∧
          x * aeval f t = aeval f p) →
        (∀ i, s ∈ (R i).integers) →
        (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → s ∈ V) →
        ∃ (lp lm : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F)
          (a : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → Fin m₀ → L),
          (∀ σ, ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
            (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
            lp σ * aeval f t = aeval f p) ∧
          (∀ σ, ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
            (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
            lm σ * aeval f⁻¹ t = aeval f⁻¹ p) ∧
          (∀ σ k, a σ k ∈ A) ∧
          x * s = ∑ σ, lp σ * z σ + ∑ σ, lm σ * ((f⁻¹) ^ m₀ * z σ) +
            ∑ σ, ∑ k : Fin m₀, algebraMap L F (a σ k) * ((f⁻¹) ^ (k : ℕ) * z σ) :=
  H1Sol.main R hR f hf htrL hfd htr heq

end S_AlgebraicCurve_RegularProlongation_exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq (solution)
