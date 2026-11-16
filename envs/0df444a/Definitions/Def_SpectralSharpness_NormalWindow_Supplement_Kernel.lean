-- Prove2me | Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Kernel
-- name    : SpectralSharpness_NormalWindow_Supplement_Kernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:06:00.311082+00:00
-- url     : https://prove2.me/theorems/dbfa8725-e77b-48ef-8611-a846c8eed7b5
-- title:
--   Gaussian circle NTK, convolution operator and zero-output gradient flow
-- statement:
--   The input at angle a is (cos a,sin a,1) in the biased case and (cos a,sin a,0) in the unbiased case. Three independent standard Gaussian input weights and an independent standard Gaussian output weight v define the train-both-layers tangent kernel by its two Gaussian expectations. The second expectation includes v²; it is not a prescribed spectrum. The angular kernel is K(τ)=Θ(τ,0), and the closed formula is a separate function to be compared to this expectation.
--
--   The eigenvalue is λ_k=(1/π)∫₀^π K(τ)cos(kτ)dτ. The convolution operator has normalization 1/(2π), and Fourier modes are exp(ikx). The canonical zero-output flow is computed by the operator-exponential series H−exp(−tΘ)H, expanded using iterates of the actual convolution operator. Its convergence and the equation ∂_t f_t=−Θ(f_t−H), f₀=0, are conclusions of the theorem. The associated classical flow predicate describes continuous periodic functions with locally uniform time bounds; it is asserted of this computed flow rather than assumed of a freely chosen function. No coefficient solution, derivative bound or sharpness bound is included in its definition.
--
--   Set α=1/(√2π²), d(t)=√(αt). Active modes have a nonzero target coefficient. The fitted harmonic count counts positive odd modes with λ_kt≥1. The soft-versus-hard integral uses the squared difference between 1−exp(−1/s²) and the hard indicator s≤1. These definitions keep the source’s Gaussian architecture and actual dynamics separate from their asserted spectral consequences.
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, §7.1 Setup; Theorems 7.1–7.2, p. 17

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

/-- Independent standard Gaussian weights (three input/bias coordinates and output weight). -/
def gaussianWeights : Measure (Fin 4 → ℝ) :=
  Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1

def angularInput (bias : Bool) (a : ℝ) : Fin 3 → ℝ :=
  ![Real.cos a, Real.sin a, if bias then 1 else 0]
def gaussianDot (bias : Bool) (w : Fin 4 → ℝ) (a : ℝ) : ℝ :=
  ∑ i : Fin 3, w i.castSucc * angularInput bias a i
/-- The train-both-layers NTK expectation; v=w₃ is independent of the input weights. -/
def tangentKernel (bias : Bool) (a b : ℝ) : ℝ :=
  (∫ w, max 0 (gaussianDot bias w a) * max 0 (gaussianDot bias w b) ∂gaussianWeights) +
    (∑ i : Fin 3, angularInput bias a i*angularInput bias b i) *
    ∫ w, (w 3)^2 * (if 0 < gaussianDot bias w a then 1 else 0) *
      (if 0 < gaussianDot bias w b then 1 else 0) ∂gaussianWeights

def circleKernel (bias : Bool) (τ : ℝ) : ℝ := tangentKernel bias τ 0

def closedBiasedKernel (τ : ℝ) : ℝ :=
  let ρ := (1+Real.cos τ)/2
  1/Real.pi * (Real.sqrt (1-ρ^2)+ρ*(Real.pi-Real.arccos ρ)) +
    (1+Real.cos τ)*(1/4+Real.arcsin ρ/(2*Real.pi))
def eigenvalue (bias : Bool) (k : ℤ) : ℝ :=
  1/Real.pi * ∫ τ in (0:ℝ)..Real.pi, circleKernel bias τ*Real.cos ((k:ℝ)*τ)
def kernelOperator (bias : Bool) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  1/(2*Real.pi) * ∫ y, circleKernel bias (x-y)*g y ∂torusMeasure

def kernelOperatorComplex (bias : Bool) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (1/(2*(Real.pi:ℂ))) * ∫ y, (circleKernel bias (x-y):ℂ)*g y ∂torusMeasure

def fourierMode (k : ℤ) (x : ℝ) : ℂ := Complex.exp (Complex.I*(k:ℂ)*(x:ℂ))
def spectralConstant : ℝ := 1/(Real.sqrt 2*Real.pi^2)
def fittedBandwidth (t : ℝ) : ℝ := Real.sqrt (spectralConstant*t)
/-- A classical zero-output flow, specified by the actual convolution equation.
Spatial continuity/periodicity and local-in-time uniform boundedness specify the usual
continuous-function evolution space, rather than assuming its spectral solution. -/
def IsKernelFlow (bias : Bool) (f : ℝ → ℝ → ℝ) : Prop :=
  (∀ x, f 0 x=0) ∧
  (∀ t, 0 ≤ t → Continuous (f t) ∧ Function.Periodic (f t) (2*Real.pi)) ∧
  (∀ T, 0 < T → ∃ B : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x, |f t x| ≤ B) ∧
  (∀ t, 0 ≤ t → ∀ x, HasDerivWithinAt (fun s => f s x)
    (-kernelOperator bias (fun y => f t y-squareWave y) x) (Set.Ici 0) t)

/-- The operator-exponential series for the zero-output solution. This uses powers
of the actual Gaussian convolution operator, never prescribed Fourier multipliers. -/
def flowSeriesTerm (bias : Bool) (t x : ℝ) (n : ℕ) : ℝ :=
  if n=0 then 0 else -((-t)^n/(n.factorial:ℝ)) * ((kernelOperator bias)^[n] squareWave) x

def zeroFlow (bias : Bool) (t x : ℝ) : ℝ := ∑' n : ℕ, flowSeriesTerm bias t x n

def activeMode (k : ℤ) : Prop := fourier squareWave k ≠ 0

def softHardIntegral : ℝ := ∫ s in Set.Ioi (0:ℝ),
  ((1-Real.exp (-1/s^2))-(if s ≤ 1 then 1 else 0))^2/s^2

def fittedCount (t : ℝ) : ℝ :=
  (({k : ℕ | 0 < k ∧ Odd k ∧ 1 ≤ eigenvalue true (k:ℤ)*t}).ncard : ℝ)

end SpectralSharpness.NormalWindow.Supplement


