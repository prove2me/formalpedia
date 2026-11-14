-- Prove2me | Definitions.Def_PGDRevision20261113_Series
-- name    : PGDRevision20261113_Series
-- status  : Definition
-- author  : @Somehow
-- created : 2026-11-13T06:23:51.703107+00:00
-- url     : https://prove2.me/theorems/49dfb18b-db7d-4743-b690-91a7ac8e78a7
-- title:
--   Power-curvature series and increasing coefficient ratios
-- statement:
--   This module defines the power-curvature coefficients using the explicit rising product and factorial, and defines consecutive coefficient ratios. Its target records the convergent power-series expansions, explicit ratios, strict increase and limit one for exponents strictly between zero and one.
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Section 6.1, Lemma 6.2, page 16.

import Definitions.Def_PGDRevision20261113_Geometry
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology

namespace PGDRevision20261113

def powerSeriesCoefficient (c : ℝ) (n : ℕ) : ℝ :=
  (∏ j ∈ Finset.range (2 * n), (c + (j : ℝ))) / ((2 * n).factorial : ℝ)

def coefficientRatio (c : ℝ) (n : ℕ) : ℝ :=
  powerSeriesCoefficient c n / powerSeriesCoefficient c (n - 1)

def PowerSeriesCoefficientRatiosClaim : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 →
    powerSeriesCoefficient c 0 = 1 ∧
    coefficientRatio c 1 = c * (c + 1) / 2 ∧
    (∀ n : ℕ, 1 ≤ n →
      coefficientRatio c n =
        ((c + 2 * n - 2) * (c + 2 * n - 1)) / (2 * n * (2 * n - 1))) ∧
    StrictMonoOn (coefficientRatio c) (Set.Ici 1) ∧
    Tendsto (coefficientRatio c) atTop (𝓝 (1 : ℝ)) ∧
    (∀ u ∈ Set.Ico (0 : ℝ) 1,
      HasSum (fun n : ℕ => powerSeriesCoefficient c n * u ^ n)
        (powerCurvature c (Real.sqrt u))) ∧
    ∀ a u : ℝ, 0 < a → a < 1 → u ∈ Set.Ico (0 : ℝ) 1 →
      HasSum (fun n : ℕ =>
        powerSeriesCoefficient c n * (coefficientRatio c (n + 1) - a) * u ^ (n + 1))
        ((1 - a * u) * powerCurvature c (Real.sqrt u) - 1)

end PGDRevision20261113


