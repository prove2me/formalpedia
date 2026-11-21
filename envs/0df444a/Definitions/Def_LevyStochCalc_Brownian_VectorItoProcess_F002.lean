-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F002
-- name    : LevyStochCalc_Brownian_VectorItoProcess_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:26:18.834576+00:00
-- url     : https://prove2.me/theorems/9ebaca05-0633-43ef-aebf-401218eda80f
-- title:
--   Source declarations: LevyStochCalc.Brownian.VectorItoProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.VectorItoProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F001
import Definitions.Def_SourceProof_4ef3e5b73189336215f644cf
import Definitions.Def_SourceProof_ca47293a4e2de3cbd71da814

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
/-- The cube of the absolute increment of the martingale part is integrable. -/
theorem integrable_abs_vectorItoMartingale_sub_pow_three (m : Fin n) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u < v) :
    Integrable (fun ω => |vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
      - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω| ^ 3) P := by
  have hint := _root_.Prove2MeSourceProof.h_ca47293a4e2de3cbd71da814 (P := P)
    (f := fun (k : Fin d) ω => coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
      - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω)
    (fun k => (measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v).sub
      (measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u))
    (fun k => (_root_.Prove2MeSourceProof.h_4ef3e5b73189336215f644cf (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k)
      (hHs m k) hC0 (hCH m k) hu huv).1)
  simp_rw [vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs m u v]
  exact hint
section VectorMoments

variable (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
  (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)

end VectorMoments

end VectorProcess

end LevyStochCalc.Brownian.Ito


