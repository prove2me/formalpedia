-- Prove2me | Definitions.Def_SourceProof_b0aff0c8496672a11de8686b
-- name    : SourceProof_b0aff0c8496672a11de8686b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:01:25.618054+00:00
-- url     : https://prove2.me/theorems/8cf6db8f-6a77-43b5-8166-110ec3cd96d2
-- title:
--   LevyStochCalc source module: SourceProof_b0aff0c8496672a11de8686b
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.sum_xi_mul_simpleIntegral_sub` comes from the `LevyStochCalc.Brownian.ItoAlgebraProduct` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F001

open private min_min_of_le min_min_of_le' from Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F001
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Products of simple integrands and elementary integrals against a process

Two simple integrands with a common final partition point multiply to a simple integrand carried
on their common refinement, whose evaluation is the pointwise product of the evaluations and
whose adaptedness is inherited; summing the increments of the elementary integral of one against
the coefficients of the other is the elementary integral of that product, and the difference
between an elementary integral and an `L²` Itô integral obeys the Itô isometry.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_b0aff0c8496672a11de8686b
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (G K : SimplePredictable Ω T)
    (h_eq : G.partition (Fin.last G.N) = K.partition (Fin.last K.N))
    (t : ℝ) (ω : Ω) :
    (∑ i : Fin G.N, G.ξ i ω *
        (simpleIntegral W K (min (G.partition i.succ) t) ω
          - simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = simpleIntegral W (G.mul_on_common K h_eq) t ω := by
  classical
  set π : Fin (G.mergedM K + 1) → ℝ := G.mergedπ K with hπ
  set L : Fin (G.mergedM K) → Fin G.N := G.mergedIdxMap_left K h_eq with hL
  set R : Fin (G.mergedM K) → Fin K.N := G.mergedIdxMap_right K h_eq with hR
  have hmono : StrictMono π := G.mergedπ_strictMono K
  have hLle : ∀ j, G.partition (L j).castSucc ≤ π j.castSucc :=
    G.mergedIdxMap_left_idx_le K h_eq
  have hLge : ∀ j, π j.succ ≤ G.partition (L j).succ := G.mergedIdxMap_left_idx_ge K h_eq
  -- `K`'s elementary integral, read on the merged partition
  have hK : ∀ u : ℝ, LevyStochCalc.Brownian.Ito.simpleIntegral W K u ω
      = ∑ j : Fin (G.mergedM K), K.ξ (R j) ω
        * (W.W (min (π j.succ) u) ω - W.W (min (π j.castSucc) u) ω) := by
    intro u
    rw [← K.simpleIntegral_refine_intermediate W (G.mergedM K) π ((_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 G) K)
      (h_eq ▸ (_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b G) K h_eq) hmono R (G.mergedIdxMap_right_idx_le K h_eq)
      (G.mergedIdxMap_right_idx_ge K h_eq) (G.mergedπ_refines_right K) u ω]
    rfl
  set ΔW : Fin (G.mergedM K) → ℝ := fun j =>
    W.W (min (π j.succ) t) ω - W.W (min (π j.castSucc) t) ω with hΔW
  set D : Fin G.N → Fin (G.mergedM K) → ℝ := fun i j =>
    (W.W (min (π j.succ) (min (G.partition i.succ) t)) ω
        - W.W (min (π j.castSucc) (min (G.partition i.succ) t)) ω)
      - (W.W (min (π j.succ) (min (G.partition i.castSucc) t)) ω
        - W.W (min (π j.castSucc) (min (G.partition i.castSucc) t)) ω) with hD
  have hDself : ∀ j, D (L j) j = ΔW j := by
    intro j
    have h1 : π j.castSucc ≤ π j.succ := (hmono Fin.castSucc_lt_succ).le
    have h2 : G.partition (L j).castSucc ≤ π j.castSucc := hLle j
    rw [hD, hΔW]
    simp only
    rw [min_min_of_le (hLge j), min_min_of_le (h1.trans (hLge j)),
      min_min_of_le' (h2.trans h1), min_min_of_le' h2]
    ring
  have hDzero : ∀ (j : Fin (G.mergedM K)) (i : Fin G.N), i ≠ L j → D i j = 0 := by
    intro j i hne
    have h1 : π j.castSucc ≤ π j.succ := (hmono Fin.castSucc_lt_succ).le
    have hGi : G.partition i.castSucc ≤ G.partition i.succ :=
      G.partition_strictMono.monotone Fin.castSucc_lt_succ.le
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (i.succ : Fin (G.N + 1)) ≤ (L j).castSucc := by
        rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
      have hstep : G.partition i.succ ≤ π j.castSucc :=
        (G.partition_strictMono.monotone hle).trans (hLle j)
      rw [hD]
      simp only
      rw [min_min_of_le' hstep, min_min_of_le' (hstep.trans h1),
        min_min_of_le' (hGi.trans hstep), min_min_of_le' ((hGi.trans hstep).trans h1)]
      ring
    · have hle : ((L j).succ : Fin (G.N + 1)) ≤ i.castSucc := by
        rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
      have hstep : π j.succ ≤ G.partition i.castSucc :=
        (hLge j).trans (G.partition_strictMono.monotone hle)
      rw [hD]
      simp only
      rw [min_min_of_le (hstep.trans hGi), min_min_of_le (h1.trans (hstep.trans hGi)),
        min_min_of_le hstep, min_min_of_le (h1.trans hstep)]
      ring
  calc (∑ i : Fin G.N, G.ξ i ω *
          (LevyStochCalc.Brownian.Ito.simpleIntegral W K (min (G.partition i.succ) t) ω
            - LevyStochCalc.Brownian.Ito.simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = ∑ i : Fin G.N, ∑ j : Fin (G.mergedM K), G.ξ i ω * (K.ξ (R j) ω * D i j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hK, hK, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hD]; ring
    _ = ∑ j : Fin (G.mergedM K), ∑ i : Fin G.N, G.ξ i ω * (K.ξ (R j) ω * D i j) :=
        Finset.sum_comm
    _ = ∑ j : Fin (G.mergedM K), G.ξ (L j) ω * K.ξ (R j) ω * ΔW j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single (L j)
          (fun i _ hne => by rw [hDzero j i hne, mul_zero, mul_zero])
          (fun hnm => absurd (Finset.mem_univ _) hnm), hDself j]
        ring
    _ = LevyStochCalc.Brownian.Ito.simpleIntegral W (G.mul_on_common K h_eq) t ω := by
        unfold LevyStochCalc.Brownian.Ito.simpleIntegral
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hΔW]
        rfl
section SimpleVsGeneral

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end SimpleVsGeneral

end LevyStochCalc.Brownian.Ito


