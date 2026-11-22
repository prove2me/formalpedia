-- Prove2me | Definitions.Def_MasulloRH_GaussianThetaTruncation
-- name    : MasulloRH_GaussianThetaTruncation
-- status  : Definition
-- author  : @sflicht
-- created : 2026-11-21T15:48:08.186186+00:00
-- url     : https://prove2.me/theorems/6c5bb9c8-c854-4cd2-b1c2-c90d61a75d82
-- title:
--   Finite dyadic theta sums with a rational-cutoff reflected evaluation
-- statement:
--   For $K\in\mathbb N$ and $x\in\mathbb R$, define
--
--   $$P_K(x)=2\sum_{k=1}^K\left(e^{-\pi(ke^x)^2}-3e^{-4\pi(ke^x)^2}+2e^{-16\pi(ke^x)^2}\right).$$
--
--   Also define the reflected finite approximation
--
--   $$\widetilde P_K(x)=\begin{cases}P_K(x),&x\ge-1,\\\frac{e^{-x}}2P_K(-x-\log4),&x<-1.\end{cases}$$
--
--   These are finite expressions in real elementary functions, embedded in $\mathbb C$. The rational switch at $-1$ allows shifted copies to be integrated on subintervals with rational breakpoints. The definitions contain no accuracy claim; comparison with the actual theta series and its reflection is proved separately. The finite reflected approximation can have a small jump at the cutoff, so integration must respect its piecewise definition.
--
--   **Formalization Note.** The Lean names are `MasulloRH.GaussianApproximation.thetaPartial` and `MasulloRH.GaussianApproximation.thetaPartialReflected`. The displayed positive-index sum is represented by indices $0,\ldots,K-1$ with argument $(n+1)e^x$.
-- source:
--   Finite sum from the proved theta Gaussian truncation theorem, https://prove2.me/theorems/2e9c99f7-cd06-43f7-a85b-f4d2cc422151 , for the actual mission definition https://prove2.me/definitions/6f34c003-4870-4c6a-b83e-256b289a15db . The reflected branch is chosen using the exact Poisson identity theta(x)=exp(-x)/2*theta(-x-log4), with a rational cutoff for numerical integration. Supporting definitions introduced for this contribution; no additional axioms or accuracy premises.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
open scoped BigOperators

namespace MasulloRH.GaussianApproximation
noncomputable section

/-- The finite symmetric truncation of the mission's dyadic Gaussian theta series. -/
def thetaPartial (K : ℕ) (x : ℝ) : ℂ :=
  2 * ∑ n ∈ Finset.range K,
    ((Real.exp (-Real.pi * (((n : ℝ) + 1) * Real.exp x) ^ 2) -
      3 * Real.exp (-Real.pi * (2 * (((n : ℝ) + 1) * Real.exp x)) ^ 2) +
      2 * Real.exp (-Real.pi * (4 * (((n : ℝ) + 1) * Real.exp x)) ^ 2) : ℝ) : ℂ)

/-- Evaluate on the reflected side below the rational cutoff -1. The rational
cutoff lets numerical quadrature split shifted copies at rational points. -/
def thetaPartialReflected (K : ℕ) (x : ℝ) : ℂ :=
  if -1 ≤ x then thetaPartial K x
  else ((Real.exp (-x) / 2 : ℝ) : ℂ) * thetaPartial K (-x - Real.log 4)

end
end MasulloRH.GaussianApproximation


