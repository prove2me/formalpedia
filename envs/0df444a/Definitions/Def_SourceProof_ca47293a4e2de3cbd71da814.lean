-- Prove2me | Definitions.Def_SourceProof_ca47293a4e2de3cbd71da814
-- name    : SourceProof_ca47293a4e2de3cbd71da814
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:18:26.356257+00:00
-- url     : https://prove2.me/theorems/32ce7a27-8f6d-4f71-9c69-29a40c002125
-- title:
--   LevyStochCalc source module: SourceProof_ca47293a4e2de3cbd71da814
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integrable_abs_sum_pow_three` comes from the `LevyStochCalc.Brownian.VectorItoProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcess_F000
import Definitions.Def_LevyStochCalc_Brownian_MultidimFiltered_F000
import Mathlib.Algebra.Order.Chebyshev

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vector Itô processes and the moments of their increments

A vector Itô process is `X_t = X₀ + ∫_{[0,t]} b_s ds + ∑ₖ ∫_0^t H^{·,k}_s dWᵏ_s` with values in
`Fin n → ℝ`, driven by a `d`-dimensional Brownian motion. Each coordinate's increment across a
window is a drift increment plus a finite sum of Itô-integral increments, so its moments follow
from the drift bound, the increment moments of the scalar Itô integral and Jensen's inequality
for sums; the supremum norm on `Fin n → ℝ` is then controlled coordinatewise.

## Main statements

* `LevyStochCalc.Brownian.Ito.vectorItoProcess` — the process itself.
* `LevyStochCalc.Brownian.Ito.vectorItoProcess_sub` — the coordinate increment splits into a
  drift part and a sum of Itô-integral increments.
* `LevyStochCalc.Brownian.Ito.integral_sq_vectorItoProcess_sub_le` — the coordinate second
  moment `𝔼|ΔXᵐ|² ≤ 2(BΔt)² + 2d²C²Δt`.
* `LevyStochCalc.Brownian.Ito.integral_abs_vectorItoProcess_sub_le` — the coordinate first
  absolute moment `𝔼|ΔXᵐ| ≤ BΔt + dC√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_le` and
  `LevyStochCalc.Brownian.Ito.integral_sq_norm_vectorItoProcess_sub_le` — the same two moments
  for the supremum norm of the vector increment.
* `LevyStochCalc.Brownian.Ito.integrable_norm_vectorItoProcess_sub_pow_three` — the cube of the
  norm of the increment is integrable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section PiNorm

variable {n : ℕ}

end PiNorm

section FiniteSums

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Fintype ι]


theorem _root_.Prove2MeSourceProof.h_ca47293a4e2de3cbd71da814 {f : ι → Ω → ℝ} (hfm : ∀ i, Measurable (f i))
    (hfi : ∀ i, Integrable (fun ω => |f i ω| ^ 3) P) :
    Integrable (fun ω => |∑ i, f i ω| ^ 3) P := by
  have hdom : Integrable (fun ω => (Fintype.card ι : ℝ) ^ 2 * ∑ i, |f i ω| ^ 3) P :=
    (MeasureTheory.integrable_finsetSum _ fun i _ => hfi i).const_mul _
  have hpt : ∀ ω, |∑ i, f i ω| ^ 3 ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ i, |f i ω| ^ 3 := fun ω => by
    have h1 : |∑ i, f i ω| ^ 3 ≤ (∑ i, |f i ω|) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) 3
    have h2 := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset ι))
      (f := fun i => |f i ω|) (fun j _ => abs_nonneg (f j ω)) 2
    simpa using h1.trans h2
  have hmeas : Measurable fun ω => |∑ i, f i ω| ^ 3 :=
    (Finset.measurable_sum _ fun i _ => hfm i).abs.pow_const 3
  refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
  exact hpt ω
end FiniteSums

section VectorProcess

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

section VectorMoments

variable (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
  (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)

end VectorMoments

end VectorProcess

end LevyStochCalc.Brownian.Ito


