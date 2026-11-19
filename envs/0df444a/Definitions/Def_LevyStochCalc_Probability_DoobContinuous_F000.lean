-- Prove2me | Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F000
-- name    : LevyStochCalc_Probability_DoobContinuous_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:37:06.226491+00:00
-- url     : https://prove2.me/theorems/7f21f79d-ccad-44ef-84c1-ed41d645811c
-- title:
--   Source declarations: LevyStochCalc.Probability.DoobContinuous
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.DoobContinuous. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F000
import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F001
import Definitions.Def_MathFin_Foundations_DoobLpMaximalInequality_F000
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob's `L²` maximal inequality in continuous time

For a right-continuous martingale on `[0, T]`, the supremum of the paths over the window is
square integrable, with `𝔼[sup_{t ≤ T} |M_t|²] ≤ 4 𝔼[|M_T|²]`.

The discrete inequality is `MeasureTheory.Martingale.eLpNorm_norm_runMax_le`; the passage to
continuous time samples the martingale along the dyadic partition of `[0, T]`, whose points are
increasing in the level, and uses right-continuity to identify the supremum over the window with
the supremum of the sampled maxima.

## Main statements

* `Filtration.compMono`, `martingale_compMono` — sampling along a monotone time map.
* `dyadicTime` — the dyadic partition points of `[0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Sampling along a monotone time map -/

variable (mΩ) in
/-- The filtration sampled along a monotone time map. -/
def Filtration.compMono {ι ι' : Type*} [Preorder ι] [Preorder ι']
    (ℱ : Filtration ι' mΩ) (τ : ι → ι') (hτ : Monotone τ) : Filtration ι mΩ where
  seq i := ℱ (τ i)
  mono' _ _ hij := ℱ.mono' (hτ hij)
  le' i := ℱ.le' (τ i)
@[simp] theorem Filtration.compMono_apply {ι ι' : Type*} [Preorder ι] [Preorder ι']
    (ℱ : Filtration ι' mΩ) (τ : ι → ι') (hτ : Monotone τ) (i : ι) :
    Filtration.compMono mΩ ℱ τ hτ i = ℱ (τ i) := rfl
/-- A martingale sampled along a monotone time map is a martingale for the sampled
filtration. -/
theorem martingale_compMono {ι ι' : Type*} [Preorder ι] [Preorder ι']
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {ℱ : Filtration ι' mΩ} {f : ι' → Ω → E}
    (hf : MeasureTheory.Martingale f ℱ μ) (τ : ι → ι') (hτ : Monotone τ) :
    MeasureTheory.Martingale (fun i => f (τ i)) (Filtration.compMono mΩ ℱ τ hτ) μ :=
  ⟨fun i => hf.1 (τ i), fun i j hij => hf.2 (τ i) (τ j) (hτ hij)⟩
/-! ### The dyadic partition of `[0, T]` -/

/-- The `k`-th dyadic partition point of `[0, T]` at level `n`, frozen at the horizon. -/
noncomputable def dyadicTime (T : ℝ) (n k : ℕ) : ℝ := min ((k : ℝ) * T / 2 ^ n) T
theorem dyadicTime_monotone {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : Monotone (dyadicTime T n) := by
  intro k l hkl
  refine min_le_min ?_ le_rfl
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) hT
theorem dyadicTime_nonneg {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) : 0 ≤ dyadicTime T n k :=
  le_min (by positivity) hT
theorem dyadicTime_le {T : ℝ} (n k : ℕ) : dyadicTime T n k ≤ T := min_le_right _ _
theorem dyadicTime_mem_Icc {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) :
    dyadicTime T n k ∈ Set.Icc (0 : ℝ) T :=
  ⟨dyadicTime_nonneg hT n k, dyadicTime_le n k⟩
@[simp] theorem dyadicTime_top {T : ℝ} (n : ℕ) :
    dyadicTime T n (2 ^ n) = T := by
  have h : ((2 ^ n : ℕ) : ℝ) * T / 2 ^ n = T := by
    push_cast
    field_simp
  rw [dyadicTime, h, min_self]
/-- Refining the level does not move the partition points: level `n`'s point `k` is level
`n + 1`'s point `2 * k`. -/
theorem dyadicTime_succ_two_mul {T : ℝ} (n k : ℕ) :
    dyadicTime T (n + 1) (2 * k) = dyadicTime T n k := by
  unfold dyadicTime
  congr 1
  push_cast
  rw [pow_succ]
  ring
/-! ### The sampled running maxima -/

variable {M : ℝ → Ω → ℝ} {T : ℝ}

/-- The running maximum of the sampled path over the dyadic partition of level `n`. -/
noncomputable def dyadicRunMax (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
    fun k => ‖M (dyadicTime T n k) ω‖
theorem dyadicRunMax_nonneg (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ dyadicRunMax M T n ω :=
  le_trans (norm_nonneg _)
    (Finset.le_sup' (f := fun k => ‖M (dyadicTime T n k) ω‖)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))))
/-! ### The supremum over the window -/

/-! ### Doob's `L²` inequality in continuous time -/

/-! ### Bounding the supremum over the window -/

/-! ### Finite sums -/

end LevyStochCalc.Probability


