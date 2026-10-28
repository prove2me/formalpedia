-- Prove2me | Definitions.Def_MarkovProcess_FiniteGridFoundations
-- name    : MarkovProcess_FiniteGridFoundations
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T17:55:14.780756+00:00
-- url     : https://prove2.me/theorems/80d33d65-9b7e-4c95-bdd8-e3fadee202b8
-- title:
--   Finite-grid bad-increment events and unit dyadic grids
-- statement:
--   Defines the event that at least one adjacent increment of an arbitrary finite time grid exceeds the given p-th power threshold, and defines the unit dyadic grid of rational times at a chosen mesh level. These mathematical foundations are taken byte-for-byte from Scott Armstrong’s MarkovProcess Lean source, with theorem commands separated for independent Prove2Me verification.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Time/FiniteGridIncrement.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Process.Kolmogorov

/-!
# Finite-grid increment bounds

This file supplies the finite union-bound step in a Kolmogorov--Chentsov argument. It is
independent of a particular dyadic-grid encoding: a later specialization only has to bound the
distance between adjacent grid times.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- The event that at least one adjacent increment of a finite time grid has `p`-th power at
least `ε ^ p`. -/
def finiteGridBadIncrement {T : Type*} {N : ℕ} (X : T → Ω → E)
    (grid : Fin (N + 1) → T) (p : ℝ) (ε : ℝ≥0∞) : Set Ω :=
  ⋃ i : Fin N,
    {ω | ε ^ p ≤ edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p}

/-- The dyadic grid of mesh `2⁻ⁿ` on the unit time interval. -/
def unitDyadicGrid (n : ℕ) : Fin (2 ^ n + 1) → NNRat :=
  fun i ↦ (i : ℕ) / (2 ^ n : NNRat)

end MarkovProcess


