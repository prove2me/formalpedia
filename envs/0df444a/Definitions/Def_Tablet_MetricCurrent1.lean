-- Prove2me | Definitions.Def_Tablet_MetricCurrent1
-- name    : Tablet_MetricCurrent1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:48:54.512963+00:00
-- url     : https://prove2.me/theorems/07afa4eb-9de7-4c9f-9f1e-9cf0c7c89fe4
-- title:
--   Metric Current1
-- statement:
--   Definitions and structural lemmas for Metric Current1, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/MetricCurrent1.lean

import Definitions.Def_Tablet_massOfFunctional
set_option autoImplicit false
open MeasureTheory ENNReal Filter Topology
open scoped NNReal
structure MetricCurrent1 (E : Type*) [MetricSpace E] [MeasurableSpace E] [BorelSpace E] where
-- BODY
  toFun : Form1 E → ℝ
  add_f : ∀ ω1 ω2 ω12 : Form1 E, ω1.pi = ω2.pi → ω1.pi = ω12.pi →
      (∀ x, ω12.f x = ω1.f x + ω2.f x) → toFun ω12 = toFun ω1 + toFun ω2
  smul_f : ∀ (ω ωc : Form1 E) (c : ℝ), ωc.pi = ω.pi →
      (∀ x, ωc.f x = c * ω.f x) → toFun ωc = c * toFun ω
  add_pi : ∀ ω1 ω2 ω12 : Form1 E, ω1.f = ω2.f → ω1.f = ω12.f →
      (∀ x, ω12.pi x = ω1.pi x + ω2.pi x) → toFun ω12 = toFun ω1 + toFun ω2
  smul_pi : ∀ (ω ωc : Form1 E) (c : ℝ), ωc.f = ω.f →
      (∀ x, ωc.pi x = c * ω.pi x) → toFun ωc = c * toFun ω
  continuous_pi : ∀ (f : E → ℝ) (bF : ℝ≥0) (hbF : ∀ x, |f x| ≤ (bF : ℝ)) (LF : ℝ≥0)
      (hLF : LipschitzWith LF f) (π : E → ℝ) (Lπ : ℝ≥0) (hLπ : LipschitzWith Lπ π)
      (πs : ℕ → E → ℝ) (Ls : ℕ → ℝ≥0) (hLs : ∀ n, LipschitzWith (Ls n) (πs n))
      (L0 : ℝ≥0) (hbound : ∀ n, Ls n ≤ L0)
      (hconv : ∀ x, Tendsto (fun n => πs n x) atTop (nhds (π x))),
      Tendsto (fun n => toFun ⟨f, bF, hbF, LF, hLF, πs n, Ls n, hLs n⟩) atTop
        (nhds (toFun ⟨f, bF, hbF, LF, hLF, π, Lπ, hLπ⟩))
  locality : ∀ ω : Form1 E,
      (∃ U : Set E, IsOpen U ∧ {x | ω.f x ≠ 0} ⊆ U ∧ ∃ c : ℝ, ∀ x ∈ U, ω.pi x = c) →
      toFun ω = 0
  finiteMass : massOfFunctional toFun ≠ (⊤ : ℝ≥0∞)


