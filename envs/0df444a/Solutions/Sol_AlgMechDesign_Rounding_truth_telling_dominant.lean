-- Prove2me | solution 1 for AlgMechDesign.Rounding.truth_telling_dominant
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:19:50.621009+00:00
-- url     : https://prove2.me/submissions/6e6ffe6c-c72f-4469-856d-406ef599a531

import Definitions.Def_AlgMechDesign_Rounding_Model
import Definitions.Def_AlgMechDesign_Rounding_Mechanism

set_option autoImplicit false
open AlgMechDesign.Rounding

private theorem gT_corrStar_eq {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ)
    (x : Fin k → Fin n) : gT x (corrStar x t) = makespan t x := by
  unfold gT makespan load corrStar
  congr 1
  funext l
  apply Finset.sum_congr rfl
  intro j hj
  have h := (Finset.mem_filter.mp hj).2
  rw [h]

private theorem roundUp_mono (δ : ℝ) (hδ : 0 < δ) {r s : ℝ} (h : r ≤ s) :
    roundUp δ r ≤ roundUp δ s := by
  unfold roundUp
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ)
  exact_mod_cast Int.ceil_mono (div_le_div_of_nonneg_right h (le_of_lt hδ))

private theorem rounds_dominant {n k : ℕ} [NeZero n] (a b δ : ℝ)
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (halloc : IsRoundedOptimal a b δ alloc)
    (i : Fin n) (ti di : Fin k → ℝ) (ei : ExecPlan n k)
    (hti : IsBoundedAgentType a b ti) (hdi : IsBoundedAgentType a b di)
    (hei : FeasibleExec i ti ei) (hr : RoundsLikeTruth δ i ti di ei) :
    Dominant a b alloc (roundingPay δ alloc) i ti di ei := by
  refine ⟨hdi, hei, ?_⟩
  intro d hd E di' hdi' ei' hei'
  let t := Function.update d i ti
  let w := Function.update d i di
  let u := Function.update d i di'
  have hw : IsBoundedType a b w := by
    intro l j
    by_cases hl : l = i
    · subst l
      simpa [w] using hdi j
    · simpa [w, hl] using hd l j
  have hround : roundType δ w = roundType δ t := by
    funext l j
    by_cases hl : l = i
    · subst l
      simpa [roundType, roundVec, w, t] using congrFun hr.1 j
    · simp [roundType, w, t, hl]
  have htrue :
      roundVec δ (corr i (alloc w) w (actualTimes alloc w (Function.update E i ei))) =
        corrStar (alloc w) (roundType δ t) := by
    funext j
    by_cases hj : alloc w j = i
    · simpa [roundVec, corr, corrStar, roundType, actualTimes, hj, t] using hr.2 (alloc w) j hj
    · simp [roundVec, corr, corrStar, roundType, hj, w, t]
  have hmono : gT (alloc u) (corrStar (alloc u) (roundType δ t)) ≤
      gT (alloc u) (roundVec δ (corr i (alloc u) u (actualTimes alloc u (Function.update E i ei')))) := by
    unfold gT
    apply Finset.sup'_mono_fun
    intro l hl
    apply Finset.sum_le_sum
    intro j hj
    by_cases he : alloc u j = i
    · have h := roundUp_mono δ hδ (hei' (alloc u) j he)
      simpa [corrStar, roundType, roundVec, corr, actualTimes, he, t] using h
    · simp [corrStar, roundType, roundVec, corr, he, t, u]
  simp only [utility, roundingPay, compensation, roundedBonus, add_sub_cancel_left]
  change -gT (alloc u) (roundVec δ (corr i (alloc u) u
      (actualTimes alloc u (Function.update E i ei')))) ≤
    -gT (alloc w) (roundVec δ (corr i (alloc w) w
      (actualTimes alloc w (Function.update E i ei))))
  rw [htrue]
  apply neg_le_neg
  calc
    gT (alloc w) (corrStar (alloc w) (roundType δ t)) ≤
        gT (alloc u) (corrStar (alloc u) (roundType δ t)) := by
      simpa only [gT_corrStar_eq, hround] using halloc w hw (alloc u)
    _ ≤ _ := hmono

theorem solution {n k : ℕ} [NeZero n] (a b δ : ℝ) (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (halloc : IsRoundedOptimal a b δ alloc) :
    (∀ (i : Fin n) (ti : Fin k → ℝ), IsBoundedAgentType a b ti →
      Dominant a b alloc (roundingPay δ alloc) i ti ti (fun _ => ti)) ∧
    Truthful a b alloc (roundingPay δ alloc) := by
  have h : ∀ (i : Fin n) (ti : Fin k → ℝ), IsBoundedAgentType a b ti →
      Dominant a b alloc (roundingPay δ alloc) i ti ti (fun _ => ti) := by
    intro i ti hti
    apply rounds_dominant a b δ ha hab hδ alloc halloc i ti ti (fun _ => ti) hti hti
    · intro x j hj
      exact le_rfl
    · exact ⟨rfl, fun _ _ _ => rfl⟩
  refine ⟨h, ?_⟩
  intro i ti hti
  exact ⟨fun _ => ti, h i ti hti⟩
