-- Prove2me | solution 1 for AGT.constant_sum_external_regret
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-12T16:36:22.436075+00:00
-- url     : https://prove2.me/submissions/a26c25a6-c183-4f81-bf31-1c5e9885b885

import Definitions.Def_agt_regret
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Matrix.Basic

namespace AGT

open Finset

end AGT

open AGT Finset in
theorem solution {m n : ℕ}
    (S : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (v : ℝ)
    (hv : ∃ p ∈ stdSimplex ℝ (Fin (m + 1)),
      ∀ y : Fin (n + 1), ∑ k, p k * S k y ≤ v)
    (T : ℕ) (q : ℕ → Fin (n + 1) → ℝ) (hq : ∀ t, t < T → IsLottery (q t))
    (A : OnlineAlgorithm (m + 1)) (R : ℝ)
    (hreg : ∀ k, algLoss A (fun t => S.mulVec (q t)) T ≤
      actionLoss (fun t => S.mulVec (q t)) k T + R) :
    algLoss A (fun t => S.mulVec (q t)) T ≤ v * T + R := by
  classical
  obtain ⟨p, hp, hpv⟩ := hv
  obtain ⟨hp0, hp1⟩ := hp
  set ℓ : ℕ → Fin (m + 1) → ℝ := fun t => S.mulVec (q t) with hℓ
  set L := algLoss A ℓ T with hLdef
  -- Step 1: at each time the `p`-average of the instantaneous losses is `≤ v`.
  have step : ∀ t ∈ range T, ∑ k, p k * ℓ t k ≤ v := by
    intro t ht
    obtain ⟨hq0, hq1⟩ := hq t (mem_range.mp ht)
    have e1 : ∑ k, p k * ℓ t k = ∑ y, q t y * (∑ k, p k * S k y) := by
      simp only [hℓ, Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun k _ => by ring
    calc ∑ k, p k * ℓ t k = ∑ y, q t y * (∑ k, p k * S k y) := e1
      _ ≤ ∑ y, q t y * v :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpv y) (hq0 y)
      _ = v := by rw [← Finset.sum_mul, hq1, one_mul]
  -- Step 2: the `p`-average of the action benchmarks is at most `v * T`.
  have hbench : ∑ k, p k * actionLoss ℓ k T ≤ v * T := by
    have e2 : ∑ k, p k * actionLoss ℓ k T = ∑ t ∈ range T, ∑ k, p k * ℓ t k := by
      simp only [actionLoss, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [e2]
    calc ∑ t ∈ range T, ∑ k, p k * ℓ t k ≤ ∑ _t ∈ range T, v :=
          Finset.sum_le_sum step
      _ = v * T := by rw [Finset.sum_const, card_range, nsmul_eq_mul]; ring
  -- Step 3: average the regret bound with the weights `p`.
  have h1 : L = ∑ k, p k * L := by rw [← Finset.sum_mul, hp1, one_mul]
  have h2 : ∑ k, p k * L ≤ ∑ k, p k * (actionLoss ℓ k T + R) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hreg k) (hp0 k)
  have h3 : ∑ k, p k * (actionLoss ℓ k T + R)
      = (∑ k, p k * actionLoss ℓ k T) + R := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul]
  linarith [h1, h2, h3, hbench]
