-- Prove2me | solution 1 for Auto.aux_setIntegral_sum_overlapContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:50:50.392149+00:00
-- url     : https://prove2.me/submissions/009297ac-24bc-4e0a-8b0e-24d264cc2430

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_mem_commonOverlapSet_iff
public import Theorems.Thm_Auto_aux_commonOverlapSet_subset_scale
public import Theorems.Thm_Auto_aux_overlapContribution_eq_indicator
public import Theorems.Thm_Auto_aux_integral_sum_overlapContribution
section
@[expose] public section
namespace Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
@[simp] private theorem aux_orbit_zero {X : Type*} (S : Fin 0 → X → X)
    (k : Fin 0 → ℕ) : aux_orbit S k = id :=
  rfl
@[simp] private theorem aux_orbit_succ {X : Type*} {n : ℕ}
    (S : Fin (n + 1) → X → X) (k : Fin (n + 1) → ℕ) :
    aux_orbit S k = (S 0)^[k 0] ∘
      aux_orbit (fun i ↦ S i.succ) (fun i ↦ k i.succ) :=
  rfl
section
universe v
end
namespace aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
end aux_CuboidNorm
namespace aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
end aux_ErgodicBox
end
end Auto
end
end

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ}
    (hn : 0 < n) {ε δ : ℝ} (hεδ : ε ≤ δ) (hwidth : ε + δ < 1)
    (a : Fin n → aux_ZVector n → ℝ) (k : aux_ZVector n)
    (u : aux_RVector n) (N : ℕ) (hu : ∀ i, 0 ≤ u i ∧ u i < ε) :
    ∫ s in Ico (0 : ℝ) N, ∑ q : Fin N,
        aux_overlapContribution ε δ a k u q.val s =
      aux_overlapWidth hn ε δ u * ∑ q : Fin N,
        ∏ i, a i (aux_translateAxisInt k i (q.val : ℤ)) := by
  let G : ℝ → ℝ := fun s ↦ ∑ q : Fin N,
    aux_overlapContribution ε δ a k u q.val s
  calc
    ∫ s in Ico (0 : ℝ) N, G s =
        ∫ s : ℝ, (Ico (0 : ℝ) N).indicator G s := by
      rw [MeasureTheory.integral_indicator measurableSet_Ico]
    _ = ∫ s : ℝ, G s := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with s
      by_cases hs : s ∈ Ico (0 : ℝ) N
      · simp [hs]
      · have hzero : G s = 0 := by
          dsimp [G]
          apply Finset.sum_eq_zero
          intro q hq
          rw [aux_overlapContribution_eq_indicator hn ε δ a k u q.val s]
          rw [Set.indicator_of_notMem]
          intro hqmem
          exact hs (aux_commonOverlapSet_subset_scale hn hwidth u hu N q
            ((aux_mem_commonOverlapSet_iff hn u q.val).mpr hqmem))
        simp [hs, hzero]
    _ = _ := aux_integral_sum_overlapContribution hn hεδ a k u N hu
end Auto
