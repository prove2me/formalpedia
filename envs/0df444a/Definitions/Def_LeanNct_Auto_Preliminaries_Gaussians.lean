-- Prove2me | Definitions.Def_LeanNct_Auto_Preliminaries_Gaussians
-- name    : LeanNct_Auto_Preliminaries_Gaussians
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:35:51.766329+00:00
-- url     : https://prove2.me/theorems/e02b50b8-00b3-4e07-a529-ece22e0aacd3
-- title:
--   Gaussians
-- statement:
--   Definitions and structural lemmas for Gaussians, from Floris van Doorn, Polona Durcik, Joris Roos, Lenka Slavíková, Christoph Thiele (roos-j/lean-nct; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Norm-variation of multiple ergodic averages for commuting transformations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_Notation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
def gaussianRescale (t : ℝ) : ℝ → ℝ := fun x => t⁻¹ * gaussian (t⁻¹ * x)
def C_gaussianBumpDecay (m N : ℕ) : ℝ :=
  Real.rpow (38 * ((m + 1 : ℕ) : ℝ)) ((m : ℝ) / 2) *
    Real.rpow (4 * ((N + 1 : ℕ) : ℝ)) ((N : ℝ) / 2)
def sqrtOneMinusGaussian (x : ℝ) : ℝ := Real.sqrt (1 - gaussian x)
def poissonKernel (x : ℝ) : ℝ := 2 * (1 + (2 * Real.pi * x) ^ 2)⁻¹
def aux_poissonFrequency (ξ : ℝ) : ℝ := Real.exp (-|ξ|)
def auxiliaryFunctionB (ξ : ℝ) : ℝ :=
  1 - sqrtOneMinusGaussian ξ - Real.exp (-|Real.sqrt Real.pi * ξ|)
def auxiliaryFunctionBDerivative (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    (-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x) +
      Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
        Real.exp (-|Real.sqrt Real.pi * x|)
def aux_BSecondNumerator (x : ℝ) : ℝ :=
  Real.pi * x ^ 2 - (1 - gaussian x) +
    (1 - Real.pi * x ^ 2) * (1 - gaussian x) ^ 2
def auxiliaryFunctionBSecondDerivative (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
        (2 * sqrtOneMinusGaussian x) +
      (-2 * Real.pi * x * gaussian x) ^ 2 /
        (4 * sqrtOneMinusGaussian x ^ 3) -
      Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)
noncomputable def aux_sqrtGaussianCoefficient (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * Ring.choose (1 / 2 : ℝ) (n + 1)
def aux_sqrtGaussianFrequencyProfile (ξ : ℝ) : ℂ :=
  (1 - sqrtOneMinusGaussian ξ : ℝ)
def aux_sqrtGaussianKernel : ℝ → ℂ :=
  FourierTransformInv.fourierInv aux_sqrtGaussianFrequencyProfile
def aux_sqrtGaussianDecayKernel (x : ℝ) : ℝ := (aux_sqrtGaussianKernel x).re
def aux_scaledPoissonFrequency (ξ : ℝ) : ℝ :=
  aux_poissonFrequency (Real.sqrt Real.pi * ξ)
def aux_scaledPoissonKernel (x : ℝ) : ℝ :=
  (Real.sqrt Real.pi)⁻¹ * poissonKernel ((Real.sqrt Real.pi)⁻¹ * x)
def C_squareRootGaussianDecay : ℝ := 17
end
end Auto


