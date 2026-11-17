-- Prove2me | Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
-- name    : Kyprianou_Ch07_DriftOscillationObservables
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:43:41.153823+00:00
-- url     : https://prove2.me/theorems/a9ac743e-b35f-447b-93ce-89a3df7e762e
-- title:
--   Chapter 7 drift and oscillation integrals and path predicates
-- statement:
--   Auxiliary formal observables for Theorem 7.1. The two nonnegative-valued improper integrals integrate t^{-1}P(X_t≥0) and t^{-1}P(X_t≤0) over t>1. Path predicates express almost sure drift to plus/minus infinity, or almost-sure unbounded positive and negative excursions along arbitrarily late time intervals. Also defines IsNontrivialLevyProcess: some increment is nonzero with positive probability, excluding the identically-zero law.
-- source:
--   Kyprianou (2006), Theorem 7.1, printed p.180, Ky.pdf landscape sheet 95 (original physical single-page p.189).

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Theorem 7.1(i): the upper-sign integral over times t>1. -/
noncomputable def nonnegativeSignIntegral
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : ENNReal :=
  ∫⁻ t : Real in Set.Ioi (1 : Real),
    ENNReal.ofReal (1 / t) *
      P {omega : Omega | 0 ≤ X (Real.toNNReal t) omega}

/-- Theorem 7.1(ii): the lower-sign integral over times t>1. -/
noncomputable def nonpositiveSignIntegral
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : ENNReal :=
  ∫⁻ t : Real in Set.Ioi (1 : Real),
    ENNReal.ofReal (1 / t) *
      P {omega : Omega | X (Real.toNNReal t) omega ≤ 0}

/-- Almost sure drift to negative infinity as physical time increases. -/
def DriftsToNegInfinity
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  ∀ᵐ omega ∂P,
    Tendsto (fun t : NNReal => X t omega) atTop atBot

/-- Almost sure drift to positive infinity as physical time increases. -/
def DriftsToPosInfinity
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  ∀ᵐ omega ∂P,
    Tendsto (fun t : NNReal => X t omega) atTop atTop

/-- Almost-sure unbounded limsup and liminf along arbitrarily late times. -/
def OscillatesAtInfinity
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  ∀ᵐ omega ∂P,
    (∀ (M : Real) (T : NNReal), ∃ t : NNReal,
      T ≤ t ∧ M ≤ X t omega) ∧
    (∀ (M : Real) (T : NNReal), ∃ t : NNReal,
      T ≤ t ∧ X t omega ≤ -M)

/-- The Lévy law has a nonzero increment with positive probability.
Excludes only the identically-zero Lévy process. -/
def IsNontrivialLevyProcess
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  ∃ t : NNReal, P {omega : Omega | X t omega ≠ 0} ≠ 0

end Kyprianou.Ch07


