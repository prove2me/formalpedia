-- Prove2me | Definitions.Def_simplexRegion
-- name    : simplexRegion
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-23T12:53:56.798384+00:00
-- url     : https://prove2.me/theorems/231d5545-4532-4ae7-9466-6f2c126e07a2
-- title:
--   Joint nonnegative simplex region
-- statement:
--   The set of `n+1` nonnegative real coordinates whose sum is strictly below `T`, with one coordinate represented separately.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

def OAI.PiExponent.DeterminantContradiction.simplexRegion (n : Nat) (T : Real) : Set (Real × (Fin n → Real)) :=
  {z | 0 ≤ z.1 ∧ (∀ i, 0 ≤ z.2 i) ∧ z.1 + (∑ i, z.2 i) < T}


