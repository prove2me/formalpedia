-- Prove2me | Definitions.Def_AvramDividend_Classical_BVBUnitUniformOriginalPhysicalExcess
-- name    : AvramDividend_Classical_BVBUnitUniformOriginalPhysicalExcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T15:05:09.295016+00:00
-- url     : https://prove2.me/theorems/f953d449-8f37-41cb-819b-7e18ca2a243f
-- title:
--   Exact original finitecap uniform BV physical stopped cash surplus over drift-only grid ledger
-- statement:
--   Defines exactly the source-uniform tenth-horizon original stopped Stieltjes dividend cash plus full surviving affine terminal, minus the initial affine candidate and actual positive-reserve masked physical drift ledger L, without altering the original source, dividend strategy, ruin clock, or Stieltjes measure. Used in the formal negation of the missing-compensator zero-contact leaf.
-- source:
--   Original target 35af5d11 with X in genuine uniform unit BV source, initial reserve zero, finite cap one, discount one, T=1/10 and physical uniform grid iT/(n+2).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable def AvramDividend.Classical.bvbUnitUniformOriginalPhysicalExcess
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) : ℝ :=
  let D := barrierStrategy X 0 0
  let T : ℝ := 1 / 10
  let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
  let u : ℕ → ℕ → ℝ≥0 := fun k i =>
    ⟨(1 / 10 : ℝ) * (i : ℝ) / ((k : ℝ) + 2), by positivity⟩
  let F : ℝ :=
    (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
        Iio (T - T / ((n : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
    (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω then
      Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
     else 0)
  let Z : ℕ → ℝ := fun i => Function.leftLim
    (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω) (u n i)
  let L : ℝ :=
    ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < (1 : ℝ≥0∞) then
        Real.exp (-(u n i : ℝ)) *
          (X.drift * deriv w (Z i) - w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
  F - (w 0 + L)


