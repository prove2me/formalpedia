-- Prove2me | solution 1 for AdaptiveBaseStock.Regret.position_tail
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:04:37.233198+00:00
-- url     : https://prove2.me/submissions/1c1b158b-f203-414d-a4b1-4c8933e64779

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Model

open MeasureTheory ProbabilityTheory AdaptiveBaseStock.Regret

namespace ABSAux6

variable {τ : ℕ}

lemma pipe_sum (Q : ℝ) (p : Fin (τ - 1) → ℝ) :
    extPipe (τ := τ) Q p (τ - 1) + ∑ i : Fin (τ - 1), extPipe (τ := τ) Q p i.val
      = Q + ∑ i, p i := by
  set g : ℕ → ℝ := fun i => if h : i < τ - 1 then p ⟨i, h⟩ else 0 with hg
  have e1 : ∑ i, p i = ∑ i ∈ Finset.range (τ - 1), g i := by
    rw [← Fin.sum_univ_eq_sum_range g]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [hg, i.isLt]
  have e2 : ∀ i, extPipe (τ := τ) Q p (i + 1) = g i := by
    intro i; simp [extPipe, hg]
  rw [Fin.sum_univ_eq_sum_range (fun i => extPipe (τ := τ) Q p i) (τ - 1), add_comm,
    ← Finset.sum_range_succ, Finset.sum_range_succ', e1]
  simp only [e2]
  have : extPipe (τ := τ) Q p 0 = Q := by simp [extPipe]
  rw [this, add_comm]

lemma extPipe_nonneg (Q : ℝ) (p : Fin (τ - 1) → ℝ) (hQ : 0 ≤ Q) (hp : ∀ i, 0 ≤ p i) (i : ℕ) :
    0 ≤ extPipe (τ := τ) Q p i := by
  unfold extPipe; split_ifs
  · exact hQ
  · exact hp _
  · exact le_rfl

lemma step_inv (S d : ℝ) (x : InvVec τ) (hx : IsNonneg x) (hd : 0 ≤ d) :
    IsNonneg (step S d x) ∧ position (step S d x) ≤ max S (position x) := by
  have hQ : 0 ≤ orderQty S x := le_max_right _ _
  constructor
  · refine ⟨fun i => extPipe_nonneg _ _ hQ hx.1 _, ?_⟩
    exact add_nonneg (le_max_right _ _) (extPipe_nonneg _ _ hQ hx.1 _)
  · have hpos : position (step S d x) = max (x.2 - d) 0 + (orderQty S x + ∑ i, x.1 i) := by
      unfold position step
      simp only
      linarith [pipe_sum (τ := τ) (orderQty S x) x.1]
    rw [hpos]
    have h1 : max (x.2 - d) 0 ≤ x.2 := max_le (by linarith) hx.2
    have h2 : orderQty S x + position x = max S (position x) := by
      unfold orderQty
      rcases le_total S (position x) with h | h
      · rw [max_eq_right (by linarith), max_eq_right h]; ring
      · rw [max_eq_left (by linarith), max_eq_left h]; ring
    unfold position at h2 ⊢
    linarith


lemma step_noorder (S d : ℝ) (x : InvVec τ) (hx : IsNonneg x) (hS : S < position x) :
    position (step S d x) = position x - min d x.2 ∧
      ∀ i : Fin (τ - 1), (step S d x).1 i = extPipe (τ := τ) 0 x.1 i.val := by
  have hQ : orderQty S x = 0 := max_eq_right (by linarith)
  refine ⟨?_, fun i => by simp [step, hQ]⟩
  have hpos : position (step S d x) = max (x.2 - d) 0 + (orderQty S x + ∑ i, x.1 i) := by
    unfold position step
    simp only
    linarith [pipe_sum (τ := τ) (orderQty S x) x.1]
  rw [hpos, hQ]
  unfold position
  rcases le_total d x.2 with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]; ring

end ABSAux6

open ABSAux6 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hD : IsDemandModel P D) (hinf : HasInfiniteSupport P (D 0))
    (τ : ℕ) (hτ : 1 ≤ τ) (S : ℝ) (hS : 0 ≤ S) (x₁ : InvVec τ) (hx₁ : IsNonneg x₁)
    (t : ℕ) (ht : τ ≤ t + 1) :
    P.real {ω | S < position (run (fun _ => S) x₁ (fun n => D n ω) t)}
      ≤ demandCdf P (D 0) (position x₁ - S) ^ (t + 1 - τ) := by
  set η := position x₁ - S
  -- deterministic part
  have key : ∀ d : ℕ → ℝ, (∀ n, 0 ≤ d n) → S < position (run (fun _ => S) x₁ d t) →
      ∀ r ∈ Finset.Ico (τ - 1) t, d r ≤ η := by
    intro d hd hlast
    set x := run (fun _ => S) x₁ d with hxdef
    have hnn : ∀ j, IsNonneg (x j) := by
      intro j; induction j with
      | zero => exact hx₁
      | succ j ih => exact (step_inv S (d j) _ ih (hd j)).1
    have hback : ∀ j, S < position (x (j + 1)) → S < position (x j) := by
      intro j hj
      by_contra hc
      push_neg at hc
      have := (step_inv S (d j) _ (hnn j) (hd j)).2
      have e : x (j + 1) = step S (d j) (x j) := rfl
      rw [← e, max_eq_left hc] at this
      linarith
    have hall : ∀ j, j ≤ t → S < position (x j) := by
      intro j hj
      induction hj using Nat.decreasingInduction with
      | self => exact hlast
      | of_succ k _ ih => exact hback k ih
    have P : ∀ j, j ≤ t → (∀ i : Fin (τ - 1), i.val < j → (x j).1 i = 0) ∧
        position (x j) + ∑ r ∈ Finset.Ico (τ - 1) j, d r ≤ position x₁ := by
      intro j
      induction j with
      | zero =>
        intro _
        refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
        simp [hxdef, run]
      | succ j ih =>
        intro hj
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        have hSj := hall j (by omega)
        obtain ⟨e1, e2⟩ := step_noorder S (d j) (x j) (hnn j) hSj
        have ex : x (j + 1) = step S (d j) (x j) := rfl
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [ex, e2]
          unfold extPipe
          split_ifs with h0 h1
          · rfl
          · exact ih1 _ (by simp; omega)
          · rfl
        · rw [ex, e1]
          have hmin : 0 ≤ min (d j) (x j).2 := le_min (hd j) (hnn j).2
          by_cases hjτ : j < τ - 1
          · have : Finset.Ico (τ - 1) (j + 1) = ∅ := Finset.Ico_eq_empty (by omega)
            have h2 : Finset.Ico (τ - 1) j = ∅ := Finset.Ico_eq_empty (by omega)
            rw [this]; rw [h2] at ih2; simp at ih2 ⊢; linarith
          · push_neg at hjτ
            rw [Finset.sum_Ico_succ_top hjτ]
            -- pipeline empty at j, so on-hand = position
            have hempty : position (x j) = (x j).2 := by
              unfold position
              rw [Finset.sum_eq_zero (fun i _ => ih1 i (by omega))]; ring
            have hpos1 : S < position (x j) - min (d j) (x j).2 := by
              rw [← e1, ← ex]; exact hall (j + 1) hj
            have : min (d j) (x j).2 = d j := by
              rcases le_total (d j) (x j).2 with h | h
              · exact min_eq_left h
              · rw [min_eq_right h] at hpos1 ⊢; rw [hempty] at hpos1; linarith
            rw [this]; linarith
    intro r hr
    obtain ⟨_, h2⟩ := P t le_rfl
    have hsum := Finset.single_le_sum (f := d) (fun i _ => hd i) hr
    simp only [η]
    linarith
  -- probability part
  have hsub : {ω | S < position (run (fun _ => S) x₁ (fun n => D n ω) t)} ⊆
      ⋂ r ∈ Finset.Ico (τ - 1) t, D r ⁻¹' Set.Iic η := by
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
    exact key (fun n => D n ω) (fun n => hD.nonneg n ω) hω
  have hind := hD.indep.measure_inter_preimage_eq_mul (S := Finset.Ico (τ - 1) t)
    (sets := fun _ => Set.Iic η) (fun _ _ => measurableSet_Iic)
  have hF : ∀ ℓ, P (D ℓ ⁻¹' Set.Iic η) = P (D 0 ⁻¹' Set.Iic η) :=
    fun ℓ => (hD.identDistrib ℓ).measure_mem_eq measurableSet_Iic
  have hcard : (Finset.Ico (τ - 1) t).card = t + 1 - τ := by simp; omega
  calc P.real {ω | S < position (run (fun _ => S) x₁ (fun n => D n ω) t)}
      ≤ P.real (⋂ r ∈ Finset.Ico (τ - 1) t, D r ⁻¹' Set.Iic η) := measureReal_mono hsub
    _ = demandCdf P (D 0) η ^ (t + 1 - τ) := by
      rw [measureReal_def, hind]
      simp only [hF, Finset.prod_const, hcard, ENNReal.toReal_pow]
      rfl
