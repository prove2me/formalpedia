-- Prove2me | Definitions.Def_SourceProof_140014934910d09d0c4cd2c3
-- name    : SourceProof_140014934910d09d0c4cd2c3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:24:25.965678+00:00
-- url     : https://prove2.me/theorems/067638f7-c417-4086-a450-0e2e6a78bf69
-- title:
--   LevyStochCalc source module: SourceProof_140014934910d09d0c4cd2c3
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_abs_vectorItoMartingale_sub_le` comes from the `LevyStochCalc.Brownian.VectorItoProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F001
import Definitions.Def_SourceProof_44f5bfd0fb515ee218ff3537

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

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_140014934910d09d0c4cd2c3 (m : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Integrable (fun ω => |vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω|) P
      ∧ ∫ ω, |vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω| ∂P
        ≤ (d : ℝ) * (C * Real.sqrt (v - u)) := by
  have hk : ∀ k : Fin d,
      Integrable (fun ω => |LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω|) P
        ∧ ∫ ω, |LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω| ∂P
          ≤ C * Real.sqrt (v - u) :=
    fun k => _root_.Prove2MeSourceProof.h_44f5bfd0fb515ee218ff3537 (W.W k) ℱ (hcoord k) (H m k) (hHm m k)
      (hHp m k) (hHs m k) hC0 (hCH m k) hu huv
  obtain ⟨hint, hle⟩ := LevyStochCalc.Brownian.Ito.integrable_abs_sum_and_le (P := P)
    (f := fun (k : Fin d) ω => LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
      - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω)
    (fun k => (LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v).sub
      (LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u))
    (fun k => (hk k).1)
  simp_rw [LevyStochCalc.Brownian.Ito.vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs m u v]
  refine ⟨hint, hle.trans ?_⟩
  calc ∑ k : Fin d, ∫ ω, |LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω| ∂P
      ≤ ∑ _k : Fin d, C * Real.sqrt (v - u) := Finset.sum_le_sum fun k _ => (hk k).2
    _ = (d : ℝ) * (C * Real.sqrt (v - u)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
section VectorMoments

variable (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
  (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)

end VectorMoments

end VectorProcess

end LevyStochCalc.Brownian.Ito


