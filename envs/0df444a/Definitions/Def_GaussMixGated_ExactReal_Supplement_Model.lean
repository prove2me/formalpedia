-- Prove2me | Definitions.Def_GaussMixGated_ExactReal_Supplement_Model
-- name    : GaussMixGated_ExactReal_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:08:25.720346+00:00
-- url     : https://prove2.me/theorems/a8923162-779b-42b0-b2f2-5728e3b02991
-- title:
--   Quantized observations, encoding lengths and smoothed rational output laws
-- statement:
--   For dimension $d$, component bound $k$ and rational parameters $\alpha,\varepsilon,\delta$, define
--   $$A=2+d+k+\alpha^{-1}+\varepsilon^{-1}+\log(1/\delta),\quad
--   \bar A=2+d+k+\lceil\alpha^{-1}\rceil+\lceil\varepsilon^{-1}\rceil+\lceil\log_2(1/\delta)\rceil,$$
--   $$b=C\big[(\lceil\log_2\bar A\rceil)^2+\lceil\log_2(1/\delta)\rceil+1\big],\qquad
--   Q_b(x)_i=2^{-b}\lfloor2^b x_i\rfloor.$$
--   Here $\log$ is natural; floor rounds negative coordinates toward negative infinity. Parameters are encoded as the rational list $(d,k,\alpha,\varepsilon,\delta)$; each observation is encoded coordinatewise in the same self-delimiting code. The trainer sees only these bits. Its run-dependent length $L$ includes the parameters and all oracle answers fetched, including their integer parts. A universal polynomial envelope is $p(AL)^p$.
--
--   A fixed rational RAM sampler reads the emitted bit-string description and uses an independent fair-coin tape. Its output is decoded as $d$ rationals and embedded into $\mathbb R^d$; its law is $Q$. Smoothing is the law of the sum of an independent $Q$ draw and a vector with law $N(0,\tau^2 I_d)$. This defines the convolution used in Theorem A.1, outside the finite-bit machine. Invalid codes decode as zero and nonhalting runs have a totalized final state; Theorem A.1 separately excludes both cases on every tape.
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, Appendix A computational model, PDF p. 23 (printed p. 21)

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Supplement_BitMachine
import Definitions.Def_GaussMixGated_ExactReal_Mixture

open MeasureTheory BlottoFPTAS.Main

noncomputable section

namespace GaussMixGated.ExactReal.Supplement

/-- The real size parameter A in Theorem A.1; log is the natural logarithm. -/
def sizeA (d k : ℕ) (α ε δ : ℚ) : ℝ :=
  2 + (d : ℝ) + k + (α : ℝ)⁻¹ + (ε : ℝ)⁻¹ + Real.log (1 / (δ : ℝ))

/-- Logarithm to base two, used only for the fractional precision. -/
def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- The integer Ā. Natural ceilings agree with integer ceilings on the theorem's domain. -/
def sizeABar (d k : ℕ) (α ε δ : ℚ) : ℕ :=
  2 + d + k + ⌈α⁻¹⌉₊ + ⌈ε⁻¹⌉₊ + ⌈logTwo (1 / (δ : ℝ))⌉₊

/-- One precision, fixed before any observation is drawn. -/
def precision (C d k : ℕ) (α ε δ : ℚ) : ℕ :=
  C * (⌈logTwo (sizeABar d k α ε δ : ℝ)⌉₊ ^ 2 +
    ⌈logTwo (1 / (δ : ℝ))⌉₊ + 1)

/-- Coordinatewise floor quantization, including for negative coordinates. -/
def quantize {d : ℕ} (b : ℕ) (x : EuclideanSpace ℝ (Fin d)) : Fin d → ℚ :=
  fun i => (⌊(2 : ℝ) ^ b * x i⌋ : ℚ) / (2 : ℚ) ^ b

/-- Fixed binary parameter layout: d, k, α, ε, δ, all in the published rational code. -/
def parameterCode (d k : ℕ) (α ε δ : ℚ) : List Bool :=
  BitRAM.encRats [(d : ℚ), (k : ℚ), α, ε, δ]

/-- The only information the trainer receives about sample number n is this encoded quantized
vector. Integer parts, signs, numerators and denominators are all included. -/
def answerCode {d : ℕ} (b : ℕ) (xs : ℕ → EuclideanSpace ℝ (Fin d)) : ℕ → List Bool :=
  fun n => BitRAM.encRats (List.ofFn (quantize b (xs n)))

/-- The first halted trainer configuration. -/
def trainFinal (T : BitProgram) (C d k : ℕ) (α ε δ : ℚ)
    (xs : ℕ → EuclideanSpace ℝ (Fin d)) (coins : ℕ → Bool) : BitState :=
  bitFinal T (parameterCode d k α ε δ) (answerCode (precision C d k α ε δ) xs) coins

/-- L is the total length of the parameters and all oracle answers fetched on this execution,
including each observation's integer part. The input stream only grows at an `obs` instruction. -/
def encodingLength (s : BitState) : ℕ := s.input.length

/-- Universal polynomial envelope for all four finite-bit bounds. -/
def costBound (p : ℕ) (A : ℝ) (L : ℕ) : ℝ := (p : ℝ) * (A * L) ^ p

/-- A sampler on a finite binary description, returning a real vector whose coordinates are
rationals. Invalid output strings decode as zero; the theorem separately requires valid decoding
on every tape and actual halting. -/
def discreteOutput (d : ℕ) (S : BitRAM.Program) (description : List Bool)
    (coins : ℕ → Bool) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (BitRAM.toAlloc d (BitRAM.output S description coins))

/-- Q is the law of the decoded rational output under independent fair coins. -/
def discreteLaw (d : ℕ) (S : BitRAM.Program) (description : List Bool) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  BitRAM.coinTape.map (discreteOutput d S description)

/-- Convolution as the law of the sum of two independent vectors. The ideal Gaussian is a
mathematical smoothing law; it is not an instruction of either finite-bit machine. -/
def smoothedLaw (d : ℕ) (S : BitRAM.Program) (description : List Bool) (τ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  ((discreteLaw d S description).prod (gaussLaw d τ 0)).map (fun z => z.1 + z.2)

end GaussMixGated.ExactReal.Supplement


