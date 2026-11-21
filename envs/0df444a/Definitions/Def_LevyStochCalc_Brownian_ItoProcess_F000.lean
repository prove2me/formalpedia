-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoProcess_F000
-- name    : LevyStochCalc_Brownian_ItoProcess_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:16:28.991956+00:00
-- url     : https://prove2.me/theorems/70749fab-6fd4-48a1-b800-1a04993fa340
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_DriftIncrement_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002
import Definitions.Def_LevyStochCalc_Probability_AbsMoment_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô processes and the moments of their increments

An Itô process is `X_t = X₀ + ∫_{[0,t]} b_s ds + ∫_0^t H_s dW_s` for a bounded drift `b` and an
`L²` integrand `H`. Its increment across a window is the drift's window integral plus the Itô
integral's increment, so its moments follow from the drift bound and the increment moments of
the Itô integral.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoProcess` — the process itself.
* `LevyStochCalc.Brownian.Ito.itoProcess_sub` — the increment splits into drift and martingale
  parts.
* `LevyStochCalc.Brownian.Ito.integral_sq_itoProcess_sub_le` — `𝔼|ΔX|² ≤ 2B²(Δt)² + 2C²Δt`.
* `LevyStochCalc.Brownian.Ito.integral_abs_sub_stochasticIntegral_le` — `𝔼|ΔM| ≤ C√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integral_abs_itoProcess_sub_le` — `𝔼|ΔX| ≤ BΔt + C√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integrable_abs_itoIncrement_pow_three` — the cube of the absolute
  increment is integrable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- `(a + b)³ ≤ 4(a³ + b³)` for nonnegative reals. -/
theorem add_pow_three_le_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [sq_nonneg (a - b), mul_nonneg ha hb, sq_nonneg (a + b)]
section Drift

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The `n`-th power of the absolute increment of a bounded drift's integral is integrable. -/
theorem integrable_abs_drift_pow
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) (n : ℕ) :
    MeasureTheory.Integrable
      (fun ω : Ω => |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ^ n) P := by
  have hDmeas : Measurable fun ω : Ω => ∫ s in Set.Ioc u v, bdrift ω s ∂volume :=
    measurable_setIntegral_Ioc hbm _ _
  have hvu : (0 : ℝ) ≤ v - u := sub_nonneg.mpr huv
  refine (MeasureTheory.integrable_const ((B * (v - u)) ^ n)).mono
    ((hDmeas.abs.pow_const n).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (abs_nonneg _) n),
    abs_of_nonneg (pow_nonneg (mul_nonneg hB0 hvu) n)]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (_root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a (Measurable.of_uncurry_left hbm) (hB ω) huv) n
/-- The cube of the absolute increment of a bounded drift's integral is integrable. -/
theorem integrable_abs_drift_pow_three
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    MeasureTheory.Integrable
      (fun ω : Ω => |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ^ 3) P :=
  integrable_abs_drift_pow (P := P) bdrift hbm hB0 hB huv 3
/-- The absolute increment of a bounded drift's integral is integrable. -/
theorem integrable_abs_drift
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    MeasureTheory.Integrable
      (fun ω : Ω => |∫ s in Set.Ioc u v, bdrift ω s ∂volume|) P := by
  simpa only [pow_one] using integrable_abs_drift_pow (P := P) bdrift hbm hB0 hB huv 1
/-- The square of the increment of a bounded drift's integral is integrable. -/
theorem integrable_drift_sq
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    MeasureTheory.Integrable
      (fun ω : Ω => (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2) P := by
  simpa only [sq_abs] using integrable_abs_drift_pow (P := P) bdrift hbm hB0 hB huv 2
/-- The first absolute moment of a bounded drift's increment is at most `B·(v − u)`. -/
theorem integral_abs_drift_le
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    ∫ ω, |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ∂P ≤ B * (v - u) := by
  calc ∫ ω, |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ∂P
      ≤ ∫ _ω : Ω, B * (v - u) ∂P :=
        MeasureTheory.integral_mono (integrable_abs_drift (P := P) bdrift hbm hB0 hB huv)
          (MeasureTheory.integrable_const _)
          (fun ω => _root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a (Measurable.of_uncurry_left hbm) (hB ω) huv)
    _ = B * (v - u) := by simp
/-- The second moment of a bounded drift's increment is at most `(B·(v − u))²`. -/
theorem integral_drift_sq_le
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    ∫ ω, (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2 ∂P ≤ (B * (v - u)) ^ 2 := by
  calc ∫ ω, (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2 ∂P
      ≤ ∫ _ω : Ω, (B * (v - u)) ^ 2 ∂P := by
        refine MeasureTheory.integral_mono (integrable_drift_sq (P := P) bdrift hbm hB0 hB huv)
          (MeasureTheory.integrable_const _) fun ω => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (_root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a (Measurable.of_uncurry_left hbm) (hB ω) huv) 2
    _ = (B * (v - u)) ^ 2 := by simp
end Drift

section Process

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- The Itô process `X_t = X₀ + ∫_{[0,t]} b_s ds + ∫_0^t H_s dW_s`. -/
noncomputable def itoProcess (X₀ : Ω → ℝ) (bdrift : Ω → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  X₀ ω + (∫ s in Set.Icc (0 : ℝ) t, bdrift ω s ∂volume)
    + stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
include hℱ in
/-- An Itô process is measurable in the sample point at each time. -/
theorem measurable_itoProcess {X₀ : Ω → ℝ} (hX₀ : Measurable X₀) {bdrift : Ω → ℝ → ℝ}
    (hbm : Measurable (Function.uncurry bdrift)) (t : ℝ) :
    Measurable (itoProcess W ℱ hℱ H hm hp hq X₀ bdrift t) := by
  unfold itoProcess
  exact (hX₀.add (measurable_setIntegral hbm _)).add
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq t).mono (ℱ.le t)).measurable
include hℱ in
/-- The increment of an Itô process is the drift's increment plus the Itô integral's. -/
theorem itoProcess_sub (X₀ : Ω → ℝ) (bdrift : Ω → ℝ → ℝ)
    (hbm : Measurable (Function.uncurry bdrift)) {B : ℝ}
    (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (ω : Ω) :
    itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
        - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω
      = (∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) := by
  unfold itoProcess
  rw [← setIntegral_Icc_sub_Icc (Measurable.of_uncurry_left hbm) (hB ω) hu huv]
  ring
variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end Process

end LevyStochCalc.Brownian.Ito


