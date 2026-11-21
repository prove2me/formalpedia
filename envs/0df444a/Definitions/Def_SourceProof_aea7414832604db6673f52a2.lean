-- Prove2me | Definitions.Def_SourceProof_aea7414832604db6673f52a2
-- name    : SourceProof_aea7414832604db6673f52a2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:30:53.971448+00:00
-- url     : https://prove2.me/theorems/e84b840b-6580-4cfb-946c-aa493b322e81
-- title:
--   LevyStochCalc source module: SourceProof_aea7414832604db6673f52a2
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integrable_norm_vectorItoProcess_sub_pow_three` comes from the `LevyStochCalc.Brownian.VectorItoProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F003
import Definitions.Def_SourceProof_5772ba714260d30ff9581e64

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

include hbm hC0 hCH hB0 hB in

theorem _root_.Prove2MeSourceProof.h_aea7414832604db6673f52a2 {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Integrable (fun ω => ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
      - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ^ 3) P := by
  have hcm : ∀ m : Fin n,
      Integrable (fun ω => |LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m| ^ 3) P := fun m =>
    LevyStochCalc.Brownian.Ito.integrable_abs_vectorItoProcess_sub_pow_three W ℱ hcoord H hHm hHp hHs hC0 hCH X₀ bdrift hbm
      hB0 hB m hu huv
  have hdom : Integrable (fun ω => (n : ℝ) ^ 2 * ∑ m : Fin n,
      |LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m| ^ 3) P :=
    (MeasureTheory.integrable_finsetSum _ fun m _ => hcm m).const_mul _
  have hpt : ∀ ω, ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ^ 3
      ≤ (n : ℝ) ^ 2 * ∑ m : Fin n,
        |LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m| ^ 3 := fun ω => by
    simpa using LevyStochCalc.Brownian.Ito.cube_norm_pi_le_sum_abs_cube
      (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω)
  have hmeas : Measurable fun ω => ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
      - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ^ 3 :=
    ((_root_.Prove2MeSourceProof.h_5772ba714260d30ff9581e64 W ℱ hcoord H hHm hHp hHs X₀ bdrift hbm hB hu
      huv.le).norm).pow_const 3
  refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 3)]
  exact hpt ω
end VectorMoments

end VectorProcess

end LevyStochCalc.Brownian.Ito


