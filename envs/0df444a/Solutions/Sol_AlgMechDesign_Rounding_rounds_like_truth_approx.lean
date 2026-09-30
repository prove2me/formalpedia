-- Prove2me | solution 1 for AlgMechDesign.Rounding.rounds_like_truth_approx
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:23:06.817754+00:00
-- url     : https://prove2.me/submissions/cabfbe51-69e7-42a2-b80a-13dbf17edfc8

import Definitions.Def_AlgMechDesign_Rounding_Model
import Definitions.Def_AlgMechDesign_Rounding_Mechanism

set_option autoImplicit false
open AlgMechDesign.Rounding

private theorem rounding_bounds (a ε δ r : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδε : δ ≤ ε * a) (hr : a ≤ r) :
    r ≤ roundUp δ r ∧ roundUp δ r ≤ (1 + ε) * r := by
  have hlo := Int.le_ceil (r / δ)
  have hhi := Int.ceil_lt_add_one (r / δ)
  have hlo' : r ≤ δ * (⌈r / δ⌉ : ℝ) := by
    have := (div_le_iff₀ hδ).mp hlo
    nlinarith
  have hhi' : δ * (⌈r / δ⌉ : ℝ) < r + δ := by
    have := mul_lt_mul_of_pos_left hhi hδ
    field_simp at this
    nlinarith
  change r ≤ δ * (⌈r / δ⌉ : ℝ) ∧ δ * (⌈r / δ⌉ : ℝ) ≤ (1 + ε) * r
  constructor
  · exact hlo'
  · have := mul_le_mul_of_nonneg_left hr (le_of_lt hε)
    nlinarith

theorem solution {n k : ℕ} [NeZero n] (a b ε δ : ℝ) (ha : 0 < a) (hab : a < b)
    (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε * a)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (halloc : IsRoundedOptimal a b δ alloc)
    (t : Fin n → Fin k → ℝ) (ht : IsBoundedType a b t)
    (D : Fin n → Fin k → ℝ) (hD : IsBoundedType a b D) (E : Fin n → ExecPlan n k)
    (hE : ∀ l : Fin n, FeasibleExec l (t l) (E l))
    (hR : ∀ l : Fin n, RoundsLikeTruth δ l (t l) (D l) (E l)) :
    ∀ y : Fin k → Fin n, gT (alloc D) (actualTimes alloc D E) ≤ (1 + ε) * makespan t y := by
  intro y
  have hrprof : roundType δ D = roundType δ t := by
    funext l j
    exact congrFun (hR l).1 j
  have hactual : gT (alloc D) (actualTimes alloc D E) ≤ makespan (roundType δ t) (alloc D) := by
    unfold gT makespan
    apply Finset.sup'_mono_fun
    intro l hl
    unfold load
    apply Finset.sum_le_sum
    intro j hj
    have he := (Finset.mem_filter.mp hj).2
    have heq := (hR l).2 (alloc D) j he
    change E (alloc D j) (alloc D) j ≤ roundUp δ (t l j)
    rw [he, ← heq]
    unfold roundUp
    have hlo := (div_le_iff₀ hδ).mp (Int.le_ceil ((E l (alloc D) j) / δ))
    nlinarith
  have hupper : makespan (roundType δ t) y ≤ (1 + ε) * makespan t y := by
    unfold makespan
    apply Finset.sup'_le
    intro i hi
    calc
      load (roundType δ t) y i ≤ (1 + ε) * load t y i := by
        unfold load
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        exact (rounding_bounds a ε δ (t i j) hε hδ hδε (ht i j).1).2
      _ ≤ (1 + ε) * Finset.univ.sup' Finset.univ_nonempty (load t y) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.le_sup' (load t y) hi
        · linarith
  have hopt := halloc D hD y
  rw [hrprof] at hopt
  exact hactual.trans (hopt.trans hupper)
