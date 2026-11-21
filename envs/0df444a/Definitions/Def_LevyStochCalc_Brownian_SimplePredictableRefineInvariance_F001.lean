-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F001
-- name    : LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:56:12.374178+00:00
-- url     : https://prove2.me/theorems/8d7c3577-c15e-4fde-88f2-0483b2abb25e
-- title:
--   Source declarations: LevyStochCalc.Brownian.SimplePredictableRefineInvariance
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.SimplePredictableRefineInvariance. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Refinement of a simple predictable integrand

Refining a `SimplePredictable Ω T` onto a finer partition
(`SimplePredictable.refine`), the pointwise description of the refined
integrand (`SimplePredictable.refine_eval`), and the invariance of the simple
stochastic integral under such a refinement
(`SimplePredictable.simpleIntegral_refine`), obtained by telescoping the driving
increments over each fiber of the refining index map.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Telescoping helper:** `∑ k ∈ range n, (g (k + 1) - g k) = g n - g 0`.
Used in `simpleIntegral_refine` for within-fiber telescoping. -/
private lemma sum_range_telescope_real (n : ℕ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.range n, (g (k + 1) - g k) = g n - g 0 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring
/-- **Shifted real-valued telescoping:**
`∑ k ∈ Finset.Ico a b, (g (k + 1) - g k) = g b - g a` for `a ≤ b`.
Direct corollary of `sum_range_telescope_real` via `Finset.sum_Ico_eq_sum_range`. -/
private lemma sum_Ico_telescope_real (a b : ℕ) (h : a ≤ b) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.Ico a b, (g (k + 1) - g k) = g b - g a := by
  rw [Finset.sum_Ico_eq_sum_range]
  -- ∑ k in range (b - a), (g (a + k + 1) - g (a + k)) = g b - g a
  have h_eq : (∑ k ∈ Finset.range (b - a),
      (g (a + k + 1) - g (a + k)))
      = (fun m => g (a + m)) (b - a) - (fun m => g (a + m)) 0 := by
    have := sum_range_telescope_real (b - a) (fun m => g (a + m))
    simpa [add_assoc] using this
  rw [h_eq]
  simp
  congr 1
  omega
/-- **Identity refinement preserves `simpleIntegral`:** when `M = H.N`,
`π' = H.partition`, and `idxMap = id`, the refined SimplePredictable
is structurally equal to `H`, so the simple integral is trivially
preserved. -/
lemma SimplePredictable.simpleIntegral_refine_id
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    simpleIntegral W (H.refine H.N H.partition H.partition_zero rfl
      H.partition_strictMono id (fun _ => le_refl _) (fun _ => le_refl _)) T ω
      = simpleIntegral W H T ω := rfl
/-- **Disjoint Ioc partition pieces:** for `i ≠ j` in `Fin H.N`, the
intervals `(H.partition i.castSucc, H.partition i.succ]` and
`(H.partition j.castSucc, H.partition j.succ]` are disjoint. Used by
the upcoming `simpleIntegral_refine` to derive `idxMap j = i` from
the inclusion hypotheses + a witness point. -/
lemma SimplePredictable.partition_Ioc_disjoint_of_ne {T : ℝ}
    (H : SimplePredictable Ω T) {i j : Fin H.N} (h_ne : i ≠ j) :
    Disjoint
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ))
      (Set.Ioc (H.partition j.castSucc) (H.partition j.succ)) := by
  rcases lt_trichotomy i j with h | h | h
  · exact Set.Ioc_disjoint_Ioc_of_le
      (H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h))
  · exact absurd h h_ne
  · exact (Set.Ioc_disjoint_Ioc_of_le
      (H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h))).symm
end LevyStochCalc.Brownian.Ito


