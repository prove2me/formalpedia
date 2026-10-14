-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0340_parallel1
-- name    : PNT_ZeroFree_433_0340_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:22:16.24947+00:00
-- url     : https://prove2.me/theorems/ab405714-6502-4b3a-8844-6d371fffddfa
-- title:
--   Zero-free region foundations: Descent.Marks, Descent.Overlap [0340_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Descent.Marks
--   - OAI.NumberTheory.DirichletL.Descent.Overlap
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/Marks.lean#L15-L102
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/Overlap.lean#L16-L87

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_PNT_ZeroFree_433_0147
import Definitions.Def_PNT_ZeroFree_433_0149
import Definitions.Def_PNT_ZeroFree_433_0345_parallel1
import Definitions.Def_PNT_ZeroFree_433_0377_parallel1
import Definitions.Def_PNT_ZeroFree_433_0419_parallel1
import Definitions.Def_PNT_ZeroFree_433_0475_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/Marks.lean#L15-L102
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/Overlap.lean#L16-L87
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Descent.Marks
section
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def primeSlot (L : Finset ι) (a : ι → ℂ) (A : Finset ι) : ℂ :=
  ∑ p ∈ L, if p ∈ A then a p else 0

def primeMark (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) : ℂ := ∏ i ∈ I, primeSlot (L i) (a i) A

omit [DecidableEq σ] in
@[simp] theorem primeMark_empty (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) : primeMark ∅ L a A = 1 := by
  simp [primeMark]

theorem primeMark_eq_tuple_sum (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ p ∈ I.pi L,
      ∏ i ∈ I.attach, if p i.1 i.2 ∈ A then a i.1 (p i.1 i.2) else 0 := by
  exact Finset.prod_sum I L (fun i p => if p ∈ A then a i p else 0)

theorem primeSlot_priority (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (A ∪ B) = primeSlot L a A + primeSlot L a (B \ A) := by
  unfold primeSlot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hA : p ∈ A <;> by_cases hB : p ∈ B <;> simp [hA, hB]

theorem primeMark_priority (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (A ∪ B) =
      ∑ J ∈ I.powerset, primeMark J L a A * primeMark (I \ J) L a (B \ A) := by
  unfold primeMark
  simp_rw [primeSlot_priority]
  exact Finset.prod_add _ _ I

theorem primeSlot_residual_list (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (B \ A) = primeSlot (L \ A) a B := by
  simp only [primeSlot, Finset.sum_ite_mem]
  congr 1
  ext p
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

omit [DecidableEq σ] in
theorem primeMark_residual_lists (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (B \ A) = primeMark I (fun i => L i \ A) a B := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact primeSlot_residual_list _ _ _ _

theorem primeSlot_norm_le (L A : Finset ι) (a : ι → ℂ)
    (ha : ∀ p ∈ L, ‖a p‖ ≤ 1) :
    ‖primeSlot L a A‖ ≤ ((L ∩ A).card : ℝ) := by
  simp only [primeSlot, Finset.sum_ite_mem]
  apply (norm_sum_le _ _).trans
  calc
    ∑ p ∈ L ∩ A, ‖a p‖ ≤ ∑ p ∈ L ∩ A, (1 : ℝ) :=
      Finset.sum_le_sum fun p hp => ha p (Finset.mem_inter.mp hp).1
    _ = _ := by simp

omit [DecidableEq σ] in
theorem primeMark_norm_le_divisor_count (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι)
    (hL : (I : Set σ).PairwiseDisjoint L)
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) :
    ‖primeMark I L a A‖ ≤ (2 : ℝ) ^ A.card := by
  have hdis : (I : Set σ).PairwiseDisjoint (fun i => L i ∩ A) := by
    intro i hi j hj hij
    exact (hL hi hj hij).mono (Finset.inter_subset_left) (Finset.inter_subset_left)
  have hcard : (∑ i ∈ I, (L i ∩ A).card) ≤ A.card := by
    rw [← Finset.card_biUnion hdis]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hp).2
  calc
    ‖primeMark I L a A‖ = ∏ i ∈ I, ‖primeSlot (L i) (a i) A‖ := by
      exact norm_prod _ _
    _ ≤ ∏ i ∈ I, ((L i ∩ A).card : ℝ) := by
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
        (fun i hi => primeSlot_norm_le _ _ _ (ha i hi))
    _ ≤ ∏ i ∈ I, (2 : ℝ) ^ (L i ∩ A).card := by
      apply Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
      intro i hi
      exact_mod_cast (Nat.le_of_lt (L i ∩ A).card.lt_two_pow_self)
    _ = (2 : ℝ) ^ (∑ i ∈ I, (L i ∩ A).card) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (2 : ℝ) ^ A.card := pow_le_pow_right₀ (by norm_num) hcard

end

end SevenEighths.InverseMoment

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Descent.Overlap
section
namespace OAI

namespace SevenEighths.InverseMoment

open UniqueFactorizationMonoid

section Moebius

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]

theorem moebius_squarefree_sq {P : M} (hP : Squarefree P) :
    moebius P ^ 2 = 1 := by
  rw [hP.moebius_eq, ← pow_mul, mul_comm _ 2, pow_mul]
  norm_num

theorem moebius_overlap_recovery {n P : M} (hnP : IsRelPrime n P)
    (hP : Squarefree P) : moebius n = moebius (n * P) * moebius P := by
  rw [hnP.moebius_mul, mul_assoc, ← pow_two, moebius_squarefree_sq hP, mul_one]

theorem moebius_character_overlap (ψ : M →* ℂ) {j n₀ P₀ : M}
    (hjn : IsRelPrime j n₀) (hnP : IsRelPrime n₀ P₀) (hP : Squarefree P₀) :
    (moebius (j * n₀) : ℂ) * ψ (j * n₀) * ψ (j * P₀) =
      (moebius j : ℂ) * (moebius P₀ : ℂ) * (moebius (n₀ * P₀) : ℂ) *
        ψ j ^ 2 * ψ (n₀ * P₀) := by
  have hμ : (moebius n₀ : ℂ) = (moebius (n₀ * P₀) : ℂ) * (moebius P₀ : ℂ) := by
    exact_mod_cast moebius_overlap_recovery hnP hP
  rw [hjn.moebius_mul, Int.cast_mul, map_mul, map_mul, map_mul, hμ]
  ring

theorem hybrid_mask_quotients {k P c R r : M}
    (hk : Squarefree k) (hP : Squarefree P) (hc : Squarefree c)
    (hPc : IsRelPrime P c) (hRk : R ∣ k) (hrk : r ∣ k)
    (hRP : R ∣ P) (hrc : r ∣ c) :
    ∃ k' P' c' : M,
      k = (R * r) * k' ∧ P = R * P' ∧ c = r * c' ∧
      IsRelPrime R r ∧ IsRelPrime k' (R * r) ∧
      IsRelPrime P' R ∧ IsRelPrime c' r ∧
      Squarefree k' ∧ Squarefree P' ∧ Squarefree c' := by
  have hRr : IsRelPrime R r := (hPc.of_dvd_left hRP).of_dvd_right hrc
  obtain ⟨k', hk'⟩ := hRr.mul_dvd hRk hrk
  obtain ⟨P', hP'⟩ := hRP
  obtain ⟨c', hc'⟩ := hrc
  have hks : Squarefree ((R * r) * k') := hk' ▸ hk
  have hPs : Squarefree (R * P') := hP' ▸ hP
  have hcs : Squarefree (r * c') := hc' ▸ hc
  obtain ⟨hkrel, _, hksf⟩ := squarefree_mul_iff.mp hks
  obtain ⟨hPrel, _, hPsf⟩ := squarefree_mul_iff.mp hPs
  obtain ⟨hcrel, _, hcsf⟩ := squarefree_mul_iff.mp hcs
  exact ⟨k', P', c', hk', hP', hc', hRr, hkrel.symm,
    hPrel.symm, hcrel.symm, hksf, hPsf, hcsf⟩

end Moebius

theorem inverse_eq_square_of_fourth_eq {z : ℂ} (hz : z ^ 4 = z) :
    z⁻¹ = z ^ 2 := by
  by_cases hzero : z = 0
  · simp [hzero]
  have hcube : z ^ 3 = 1 := by
    apply mul_left_cancel₀ hzero
    calc
      z * z ^ 3 = z ^ 4 := by ring
      _ = z := hz
      _ = z * 1 := by ring
  calc
    z⁻¹ = z⁻¹ * z ^ 3 := by rw [hcube, mul_one]
    _ = z ^ 2 := by field_simp

theorem inverse_cube_square_eq_sixth {z : ℂ} (h : z ^ 6 = 0 ∨ z ^ 6 = 1) :
    ((z ^ 3)⁻¹) ^ 2 = z ^ 6 := by
  rw [← inv_pow, ← pow_mul]
  norm_num
  rcases h with h | h <;> rw [h] <;> norm_num

theorem inverse_square_cube_mask {M : Type*} [Monoid M]
    (ψ : M →* ℂ) (n b : M) (h : ψ b ^ 6 = 0 ∨ ψ b ^ 6 = 1) :
    (ψ (n * b ^ 3))⁻¹ ^ 2 = (ψ n)⁻¹ ^ 2 * ψ b ^ 6 := by
  rw [map_mul, map_pow, mul_inv_rev, mul_pow, inverse_cube_square_eq_sixth h]
  ring

theorem overlap_scalar_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖z ^ 2‖ ≤ 1 := by
  rw [norm_pow]
  simpa using pow_le_pow_left₀ (norm_nonneg z) hz 2

end SevenEighths.InverseMoment

end OAI

end


