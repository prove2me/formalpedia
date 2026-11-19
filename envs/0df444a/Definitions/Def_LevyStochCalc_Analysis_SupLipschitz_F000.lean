-- Prove2me | Definitions.Def_LevyStochCalc_Analysis_SupLipschitz_F000
-- name    : LevyStochCalc_Analysis_SupLipschitz_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:57:24.59053+00:00
-- url     : https://prove2.me/theorems/9cfa1538-4efd-4ec6-a4b9-38bb92b65217
-- title:
--   Source declarations: LevyStochCalc.Analysis.SupLipschitz
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Analysis.SupLipschitz, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Suprema of Lipschitz functions

The pointwise supremum of a family of real `K`-Lipschitz functions on a pseudo-metric space,
indexed by a nonempty type and bounded above at every point, is `K`-Lipschitz.

In particular a supremum `m ↦ ⨆ i, (φ i - f i * m)` of affine functions of `m : ℝ` whose slopes
satisfy `|f i| ≤ B` is `B`-Lipschitz.

## Main statements

* `LevyStochCalc.Analysis.lipschitzWith_ciSup` — the supremum of `K`-Lipschitz functions is
  `K`-Lipschitz.
* `LevyStochCalc.Analysis.abs_ciSup_sub_mul_sub_ciSup_sub_mul_le` — the supremum of affine
  functions with slopes bounded by `B` in absolute value is `B`-Lipschitz.
-/

open scoped NNReal

namespace LevyStochCalc.Analysis

variable {ι α : Type*} [Nonempty ι] [PseudoMetricSpace α]

/-- The pointwise supremum of a family of `K`-Lipschitz real functions, indexed by a nonempty type
and bounded above at every point, is `K`-Lipschitz. -/
theorem lipschitzWith_ciSup {f : ι → α → ℝ} {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i))
    (hbdd : ∀ x, BddAbove (Set.range fun i => f i x)) :
    LipschitzWith K fun x => ⨆ i, f i x := by
  refine LipschitzWith.of_le_add_mul K fun x y => ciSup_le fun i => ?_
  calc f i x ≤ f i y + K * dist x y := (hf i).le_add_mul x y
    _ ≤ (⨆ j, f j y) + K * dist x y := by gcongr; exact le_ciSup (hbdd y) i
/-- The supremum `m ↦ ⨆ i, (φ i - f i * m)` of affine functions of `m : ℝ` whose slopes satisfy
`|f i| ≤ B`, bounded above at every point, is `B`-Lipschitz. -/
theorem abs_ciSup_sub_mul_sub_ciSup_sub_mul_le {φ f : ι → ℝ} {B : ℝ} (hfB : ∀ i, |f i| ≤ B)
    (hbdd : ∀ x : ℝ, BddAbove (Set.range fun i => φ i - f i * x)) (m m' : ℝ) :
    |(⨆ i, φ i - f i * m) - ⨆ i, φ i - f i * m'| ≤ B * |m - m'| := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hfB (Classical.arbitrary ι))
  have hlip : ∀ i, LipschitzWith B.toNNReal fun x : ℝ => φ i - f i * x := fun i =>
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal B hB,
        show φ i - f i * x - (φ i - f i * y) = -(f i * (x - y)) by ring, abs_neg, abs_mul]
      exact mul_le_mul_of_nonneg_right (hfB i) (abs_nonneg _)
  have h := (lipschitzWith_ciSup hlip hbdd).dist_le_mul m m'
  rwa [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal B hB] at h
end LevyStochCalc.Analysis


