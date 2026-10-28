-- Prove2me | solution 1 for AllocationIndices.Branching.optimalReturn_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T09:09:50.145953+00:00
-- url     : https://prove2.me/submissions/f05a9f95-b61f-458f-bc6e-c50476ba768e

import Mathlib
import Definitions.Def_AllocationIndices_Branching_Parallel
import Theorems.Thm_AllocationIndices_Branching_minCoeffSum_ge_entryDiscount
import Theorems.Thm_AllocationIndices_Branching_return_eq_coeffSum_expansion

/-!
Corollary 5.20 of Gittins, Glazebrook and Weber (2nd ed., p. 142), reduced to
Eq. (5.25) (`AllocationIndices.Branching.return_eq_coeffSum_expansion`) and
Lemma 5.19(i) (`AllocationIndices.Branching.minCoeffSum_ge_entryDiscount`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace P2MA35

open AllocationIndices AllocationIndices.Branching

variable {N n M : ℕ}

/-- A fixed selection of the first `M` arms gives a policy on `M` machines. -/
noncomputable def constPolicy (hMn : M ≤ n) : ParallelPolicy n N M where
  select _ := Kernel.const _ (Measure.dirac (fun b : Fin n ↦ decide ((b : ℕ) < M)))
  markov _ := inferInstance
  card_eq t h := by
    rw [Kernel.const_apply]
    refine Measure.dirac_apply_of_mem ?_
    show selCount (fun b : Fin n ↦ decide ((b : ℕ) < M)) = M
    unfold selCount
    have : (univ.filter fun b : Fin n ↦ decide ((b : ℕ) < M) = true) =
        univ.filter fun b : Fin n ↦ (b : ℕ) < M := by
      ext b; simp
    rw [this, Fin.card_filter_val_lt]
    omega

lemma conservationCoeff_nonneg (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (a : ℝ) (ha₀ : 0 < a) (S : Finset (Fin (N + 1))) (i : Fin (N + 1)) :
    0 ≤ conservationCoeff P a S i := by
  unfold conservationCoeff
  split_ifs
  · unfold stoppedTime
    refine integral_nonneg fun ω ↦ ?_
    unfold discountedStoppedSum
    refine tsum_nonneg fun t ↦ ?_
    split_ifs
    · positivity
    · exact le_rfl
  · exact le_rfl

lemma parallelPerformance_nonneg (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (a : ℝ) (ha₀ : 0 < a) (k : Fin n → Fin (N + 1))
    (i : Fin (N + 1)) : 0 ≤ parallelPerformance P π a k i := by
  unfold parallelPerformance
  refine tsum_nonneg fun t ↦ mul_nonneg (pow_nonneg ha₀.le t) ?_
  unfold parallelOccupation
  exact integral_nonneg fun h ↦ Nat.cast_nonneg _

lemma coeffSum_nonneg (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (a : ℝ) (ha₀ : 0 < a) (k : Fin n → Fin (N + 1))
    (S : Finset (Fin (N + 1))) : 0 ≤ coeffSum P π a k S := by
  unfold coeffSum
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (conservationCoeff_nonneg P a ha₀ S i) (parallelPerformance_nonneg P π a ha₀ k i)

lemma psi_le (arm : Fin (N + 1) → Fin n) (hM : 1 ≤ M) (hMn : M ≤ n)
    (lowest : Fin n → Fin (N + 1))
    (hlowest : ∀ b, arm (lowest b) = b ∧ ∀ j, arm j = b → lowest b ≤ j)
    (hnum : Monotone lowest) (j : Fin (N + 1))
    (hj : lowest ⟨n - M, Nat.sub_lt (lt_of_lt_of_le hM hMn) hM⟩ ≤ j) :
    psi arm j ≤ M - 1 := by
  unfold psi missedArms
  have hsub : (univ.filter fun b : Fin n ↦ ∀ l, arm l = b → j < l) ⊆
      univ.filter fun b : Fin n ↦ n - M < (b : ℕ) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    by_contra hlt
    rw [not_lt] at hlt
    have hle : b ≤ ⟨n - M, Nat.sub_lt (lt_of_lt_of_le hM hMn) hM⟩ := by
      rw [Fin.le_iff_val_le_val]; exact hlt
    have h1 := hb (lowest b) (hlowest b).1
    have h2 := hnum hle
    exact absurd (lt_of_lt_of_le h1 (h2.trans hj)) (lt_irrefl _)
  refine (Finset.card_le_card hsub).trans ?_
  have : (univ.filter fun b : Fin n ↦ n - M < (b : ℕ)).card ≤ (Finset.Ioo (n - M) n).card := by
    refine Finset.card_le_card_of_injOn (fun b ↦ (b : ℕ)) ?_ ?_
    · intro b hb
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hb
      simp only [Finset.coe_Ioo, Set.mem_Ioo]
      exact ⟨hb, b.isLt⟩
    · intro b _ c _ h
      exact Fin.ext h
  refine this.trans ?_
  rw [Nat.card_Ioo]
  omega

end P2MA35

open AllocationIndices AllocationIndices.Branching in
theorem solution {N n M : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (arm : Fin (N + 1) → Fin n) (hP : IsArmFamily P arm)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hM : 1 ≤ M) (hMn : M ≤ n)
    (r : Fin (N + 1) → ℝ) (y : Fin (N + 1) → ℝ)
    (hAG : IsAdaptiveGreedy (conservationCoeff P a) r (Equiv.refl (Fin (N + 1))) y)
    (hmono : Monotone (greedyIndex (Equiv.refl (Fin (N + 1))) y))
    (lowest : Fin n → Fin (N + 1))
    (hlowest : ∀ b, arm (lowest b) = b ∧ ∀ j, arm j = b → lowest b ≤ j)
    (hnum : Monotone lowest)
    (k : Fin n → Fin (N + 1)) (hk : ∀ b, arm (k b) = b) :
    optimalReturn P M a r k ≤
      greedyIndex (Equiv.refl (Fin (N + 1))) y (Fin.last N) * ((M : ℝ) / (1 - a)) -
      1 / (1 - a) *
        ∑ i ∈ univ.filter (fun i : Fin N ↦
            lowest ⟨n - M, Nat.sub_lt (lt_of_lt_of_le hM hMn) hM⟩ ≤ i.castSucc),
          (greedyIndex (Equiv.refl (Fin (N + 1))) y i.succ -
            greedyIndex (Equiv.refl (Fin (N + 1))) y i.castSucc) *
            ((M : ℝ) - psi arm i.castSucc) *
            aggregateEntryDiscount P a arm k i.castSucc ((M : ℝ) - psi arm i.castSucc) := by
  have : Nonempty (ParallelPolicy n N M) := ⟨P2MA35.constPolicy hMn⟩
  unfold optimalReturn
  refine ciSup_le fun π ↦ ?_
  rw [AllocationIndices.Branching.return_eq_coeffSum_expansion P a ha₀ ha₁ r y hAG k π]
  set ν := greedyIndex (Equiv.refl (Fin (N + 1))) y
  have h1a : 0 < 1 - a := by linarith
  have hd : ∀ i : Fin N, 0 ≤ ν i.succ - ν i.castSucc := fun i ↦
    sub_nonneg.2 (hmono (Fin.castSucc_le_succ i))
  have key : (1 / (1 - a)) * ∑ i ∈ univ.filter (fun i : Fin N ↦
        lowest ⟨n - M, Nat.sub_lt (lt_of_lt_of_le hM hMn) hM⟩ ≤ i.castSucc),
        (ν i.succ - ν i.castSucc) * ((M : ℝ) - psi arm i.castSucc) *
          aggregateEntryDiscount P a arm k i.castSucc ((M : ℝ) - psi arm i.castSucc) ≤
      ∑ i : Fin N, (ν i.succ - ν i.castSucc) * coeffSum P π a k (Iic i.castSucc) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_le_sum ?_
    · intro i hi
      by_cases hf : lowest ⟨n - M, Nat.sub_lt (lt_of_lt_of_le hM hMn) hM⟩ ≤ i.castSucc
      · rw [if_pos hf]
        have hψ := P2MA35.psi_le arm hM hMn lowest hlowest hnum i.castSucc hf
        have hlb := AllocationIndices.Branching.minCoeffSum_ge_entryDiscount P arm hP a ha₀ ha₁
          hM hMn k hk i.castSucc hψ
        have hmin : minCoeffSum P M a k (Iic i.castSucc) ≤ coeffSum P π a k (Iic i.castSucc) :=
          ciInf_le ⟨0, by
            rintro _ ⟨π', rfl⟩
            exact P2MA35.coeffSum_nonneg P π' a ha₀ k _⟩ π
        have := mul_le_mul_of_nonneg_left (hlb.trans hmin) (hd i)
        calc 1 / (1 - a) * ((ν i.succ - ν i.castSucc) * ((M : ℝ) - psi arm i.castSucc) *
              aggregateEntryDiscount P a arm k i.castSucc ((M : ℝ) - psi arm i.castSucc))
            = (ν i.succ - ν i.castSucc) * (((M : ℝ) - psi arm i.castSucc) / (1 - a) *
              aggregateEntryDiscount P a arm k i.castSucc ((M : ℝ) - psi arm i.castSucc)) := by
              ring
          _ ≤ _ := this
      · rw [if_neg hf]
        exact mul_nonneg (hd i) (P2MA35.coeffSum_nonneg P π a ha₀ k _)
  linarith
