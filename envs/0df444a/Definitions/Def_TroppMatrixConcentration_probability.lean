-- Prove2me | Definitions.Def_TroppMatrixConcentration_probability
-- name    : TroppMatrixConcentration_probability
-- status  : Definition
-- author  : @tc
-- created : 2026-10-07T13:43:32.744678+00:00
-- url     : https://prove2.me/theorems/e2999b81-b9a4-4b8d-b290-435415b3efbd
-- title:
--   Matrix second moments, cumulant sums, and Bernstein tail expression
-- statement:
--   Equip complex matrix spaces with the Borel sigma-algebra of their product topology. For matrix-valued functions on a measure space, define the uncentered rectangular second-moment statistic $\max\{\|\int ZZ^*\|,\|\int Z^*Z\|\}$, the Hermitian second-moment statistic $\|\int Y^2\|$, and the finite cumulant sum $K(\theta)=\sum_k\log\int e^{\theta X_k}$. Centering is supplied explicitly by callers; the concentration statements use zero-mean random matrices. The Bernstein tail expression is $d\exp(-(t^2/2)/(v+Lt/3))$ when the denominator is nonzero. When it is zero the expression is defined as $d$ at $t=0$ and zero otherwise. Probability, integrability, Hermitian, and positivity assumptions belong to the theorem statements, not to these total definitions.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Sections 2.2.4 and 2.2.6–2.2.8; equations (3.6.1–4), (6.1.1), (6.1.4), and (6.6.1–3); printed pp. 26–29, 36, 76, 96.

import Definitions.Def_TroppMatrixConcentration_spectral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace TroppMatrixConcentration

instance matrixMeasurableSpace {m n : Type*} : MeasurableSpace (Matrix m n ℂ) :=
  borel (Matrix m n ℂ)

instance matrixBorelSpace {m n : Type*} : BorelSpace (Matrix m n ℂ) := ⟨rfl⟩

def rectSecondMoment {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (μ : Measure Ω) (Z : Ω → Matrix m n ℂ) : ℝ :=
  max (spectralNorm (∫ ω, Z ω * (Z ω).conjTranspose ∂μ))
      (spectralNorm (∫ ω, (Z ω).conjTranspose * Z ω ∂μ))

def hermitianSecondMoment {Ω d : Type*} [MeasurableSpace Ω]
    [Fintype d] [DecidableEq d] (μ : Measure Ω) (Y : Ω → Matrix d d ℂ) : ℝ :=
  spectralNorm (∫ ω, Y ω ^ 2 ∂μ)

def cumulantSum {Ω d : Type*} [MeasurableSpace Ω]
    [Fintype d] [DecidableEq d] {N : ℕ}
    (μ : Measure Ω) (X : Fin N → Ω → Matrix d d ℂ) (θ : ℝ) : Matrix d d ℂ :=
  ∑ k, matrixLog (∫ ω, matrixExp (θ • X k ω) ∂μ)

def bernsteinTail (dimension : ℕ) (v L t : ℝ) : ℝ :=
  if v + L * t / 3 = 0 then
    if t = 0 then (dimension : ℝ) else 0
  else (dimension : ℝ) * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3))

end TroppMatrixConcentration


