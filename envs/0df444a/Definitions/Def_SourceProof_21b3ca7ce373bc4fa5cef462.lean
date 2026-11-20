-- Prove2me | Definitions.Def_SourceProof_21b3ca7ce373bc4fa5cef462
-- name    : SourceProof_21b3ca7ce373bc4fa5cef462
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:36:26.269069+00:00
-- url     : https://prove2.me/theorems/df5d3d08-8795-4fb4-9164-0c234fcc2bc7
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.partition_intervals_disjoint
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple predictable integrands and the elementary Brownian integral

The class `SimplePredictable` of integrands `∑_i ξ_i · 1_{(t_i, t_{i+1}]}` with bounded
measurable coefficients, their pointwise evaluation `SimplePredictable.eval`, the elementary
integral `simpleIntegral` against a scalar Brownian motion `W`, and the energy
`∫⁻ ‖H.eval s ω‖₊ ^ 2` of the integrand, which the disjointness of the partition intervals
`(t_i, t_{i+1}]` turns into the sum `∑_i (t_{i+1} - t_i) · ∫⁻ ‖ξ_i‖₊ ^ 2 ∂P`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_21b3ca7ce373bc4fa5cef462 {T : ℝ} (H : SimplePredictable Ω T) :
    Pairwise (fun i j : Fin H.N => Disjoint
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ))
      (Set.Ioc (H.partition j.castSucc) (H.partition j.succ))) := by
  intro i j hij
  -- WLOG i < j (or j < i); then partition i.succ ≤ partition j.castSucc.
  rcases lt_or_gt_of_ne hij with h | h
  · -- i < j: i.succ ≤ j.castSucc, so (t_i, t_{i+1}] is to the left of (t_j, t_{j+1}]
    have h_succ_le : H.partition i.succ ≤ H.partition j.castSucc :=
      H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    rw [Set.disjoint_iff]
    intro x ⟨hx_i, hx_j⟩
    obtain ⟨_, hx_i_le⟩ := Set.mem_Ioc.mp hx_i
    obtain ⟨hx_j_lt, _⟩ := Set.mem_Ioc.mp hx_j
    -- hx_i_le : x ≤ t_{i+1}, hx_j_lt : t_j < x. Combined with h_succ_le: contradiction.
    have : x ≤ H.partition j.castSucc := hx_i_le.trans h_succ_le
    exact absurd this (not_le.mpr hx_j_lt)
  · -- j < i: symmetric
    have h_succ_le : H.partition j.succ ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    rw [Set.disjoint_iff]
    intro x ⟨hx_i, hx_j⟩
    obtain ⟨hx_i_lt, _⟩ := Set.mem_Ioc.mp hx_i
    obtain ⟨_, hx_j_le⟩ := Set.mem_Ioc.mp hx_j
    have : x ≤ H.partition i.castSucc := hx_j_le.trans h_succ_le
    exact absurd this (not_le.mpr hx_i_lt)
end LevyStochCalc.Brownian.Ito


