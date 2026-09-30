-- Prove2me | solution 1 for AlgMechDesign.Rounding.rounding_mechanism_truthful_approx
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:24:38.457396+00:00
-- url     : https://prove2.me/submissions/f1440ef5-c72a-493f-a1d5-3923198cee07

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

private theorem truthful_corollary {n k : ℕ} [NeZero n] (a b δ : ℝ) (ha : 0 < a) (hab : a < b)
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

private theorem approximation_corollary {n k : ℕ} [NeZero n] (a b ε δ : ℝ) (ha : 0 < a) (hab : a < b)
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

theorem solution {n k : ℕ} [NeZero n] (a b ε δ : ℝ) (ha : 0 < a)
    (hab : a < b) (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε * a)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (halloc : IsRoundedOptimal a b δ alloc) :
    Truthful a b alloc (roundingPay δ alloc) ∧
    ∀ t : Fin n → Fin k → ℝ, IsBoundedType a b t →
      ∀ (D : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k),
        (∀ l : Fin n, Dominant a b alloc (roundingPay δ alloc) l (t l) (D l) (E l)) →
        (∀ l : Fin n, RoundsLikeTruth δ l (t l) (D l) (E l)) →
          ∀ y : Fin k → Fin n,
            gT (alloc D) (actualTimes alloc D E) ≤ (1 + ε) * makespan t y := by
  refine ⟨(truthful_corollary a b δ ha hab hδ alloc halloc).2, ?_⟩
  intro t ht D E hdom hround
  exact approximation_corollary a b ε δ ha hab hε hδ hδε alloc halloc t ht D
    (fun l => (hdom l).1) E (fun l => (hdom l).2.1) hround
