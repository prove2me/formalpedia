-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticCollision
-- name    : OAI_NumberTheory_PiExponent_Analysis_AnalyticCollision
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T09:30:24.480409+00:00
-- url     : https://prove2.me/theorems/82d606c5-f704-4255-8948-696d425a76a1
-- title:
--   Analytic coefficient and row-test constructions
-- statement:
--   This module defines three complex-valued constructions used in the analytic determinant estimates. For $b,h,z\in\mathbb C$ and $d\in\mathbb N$, the exponential monomial is
--
--   $$M_{b,h,d}(z)=b\,e^{hz}z^d.$$
--
--   For a function $f:\mathbb C\to\mathbb C$, a real radius $R$, and $d\in\mathbb N$, the normalized Taylor coefficient is the Cauchy-power-series coefficient of $f$ about $0$ at radius $R$, evaluated on the constant vector with value $R$. For $\ell\in\mathbb N$, the row test is the same construction at radius $1/2$, evaluated on the constant vector with value $1$. These are definitions and assume no analyticity or radius-positivity hypotheses on $f$ or $R$; later analytic bounds state the conditions they need.
-- source:
--   OpenAI math, source commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, definitions in Analysis/AnalyticCollision.lean: exponentialMonomial, lines 10-11 (https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticCollision.lean#L10-L11); normalizedTaylorCoeff, lines 31-32 (https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticCollision.lean#L31-L32); rowTest, lines 88-89 (https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticCollision.lean#L88-L89)

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Topology.Instances.Matrix


namespace OAI

open scoped BigOperators
open Complex Finset

namespace PiExponent.AnalyticCollision

noncomputable def exponentialMonomial (b h : ℂ) (d : ℕ) (z : ℂ) : ℂ :=
  b * Complex.exp (h * z) * z ^ d





noncomputable def normalizedTaylorCoeff (f : ℂ → ℂ) (R : ℝ) (d : ℕ) : ℂ :=
  cauchyPowerSeries f 0 R d (fun _ => (R : ℂ))









noncomputable def rowTest (ell : ℕ) (f : ℂ → ℂ) : ℂ :=
  cauchyPowerSeries f 0 (1 / 2) ell (fun _ => 1)











end PiExponent.AnalyticCollision

end OAI


