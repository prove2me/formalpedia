-- Prove2me | Definitions.Def_FeynmanKac_ClassicalSolutionConditions
-- name    : FeynmanKac_ClassicalSolutionConditions
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T21:50:33.049312+00:00
-- url     : https://prove2.me/theorems/fc0c4b41-6171-4144-8c0e-e016c6361676
-- title:
--   Classical PDE and finite-energy conditions for the Feynman–Kac theorem
-- statement:
--   Define the independent C1-in-time and C2-in-space smoothness requirements, a bounded solution of the actual backward Kolmogorov PDE with terminal boundary condition, and measurable finite expected quadratic energy for the discounted Brownian integrand. None of the predicates assumes the desired stochastic identity, martingale property or Feynman–Kac expectation.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula; Stanford Nolen notes §4.1

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

namespace FeynmanKac.BoundedDiffusionModel

/-- A checkable C¹-in-time, C²-in-space regularity condition.
The value and all derivatives used by the generator vary continuously
jointly in space and time. -/
def IsC12 {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (m : BoundedDiffusionModel P) (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ s, Differentiable ℝ (fun x => u x s)) ∧
  (∀ x, Differentiable ℝ (fun s => u x s)) ∧
  (∀ s, Differentiable ℝ (deriv (fun x => u x s))) ∧
  Continuous (fun z : ℝ × ℝ => u z.1 z.2) ∧
  Continuous (fun z : ℝ × ℝ => deriv (fun s => u z.1 s) z.2) ∧
  Continuous (fun z : ℝ × ℝ => deriv (fun x => u x z.2) z.1) ∧
  Continuous (fun z : ℝ × ℝ =>
    deriv (deriv (fun x => u x z.2)) z.1)

/-- A bounded classical solution of the backward terminal-value PDE.
Every requirement is analytic or terminal data; no stochastic identity
or martingale conclusion is built into this predicate. -/
def IsClassicalPDESolution {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (m : BoundedDiffusionModel P) (u : ℝ → ℝ → ℝ) : Prop :=
  m.IsC12 u ∧
  (∃ B : ℝ, ∀ x s, s ∈ Set.Icc m.initialTime m.terminalTime →
    |u x s| ≤ B) ∧
  (∀ x, u x m.terminalTime = m.terminalPayoff x) ∧
  (∀ x s, s ∈ Set.Icc m.initialTime m.terminalTime →
    deriv (fun r => u x r) s +
      m.drift x s * deriv (fun y => u y s) x +
      (1 / 2 : ℝ) * (m.volatility x s) ^ 2 *
        deriv (deriv (fun y => u y s)) x -
      m.potential x s * u x s + m.runningSource x s = 0)

/-- A uniform bound for the spatial derivative over the model's
finite time horizon. This is an analytic input for an L² estimate. -/
def BoundedSpatialGradient {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (m : BoundedDiffusionModel P) (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ x s, s ∈ Set.Icc m.initialTime m.terminalTime →
    |deriv (fun y => u y s) x| ≤ B

/-- Joint measurability and finite expected quadratic energy of the
discounted Brownian integrand σ(X_s,s) ∂ₓu(X_s,s). This is an independent
integrability hypothesis, not a claim that the integral is a martingale. -/
def SquareIntegrableDiscountedGradient
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (m : BoundedDiffusionModel P) (u : ℝ → ℝ → ℝ) : Prop :=
  Measurable
    (fun z : ℝ × Ω =>
      m.pathDiscount z.1 z.2 *
      m.volatility (m.path z.1 z.2) z.1 *
      deriv (fun x => u x z.1) (m.path z.1 z.2)) ∧
  Integrable
    (fun ω => ∫ s in m.initialTime..m.terminalTime,
      (m.pathDiscount s ω *
        m.volatility (m.path s ω) s *
        deriv (fun x => u x s) (m.path s ω)) ^ 2)
    P

end FeynmanKac.BoundedDiffusionModel


