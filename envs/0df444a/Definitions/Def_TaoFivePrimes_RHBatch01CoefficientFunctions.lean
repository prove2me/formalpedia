-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01CoefficientFunctions
-- name    : TaoFivePrimes_RHBatch01CoefficientFunctions
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T18:10:15.413585+00:00
-- url     : https://prove2.me/theorems/4c835f26-b53c-4020-8266-a0f8c454fe43
-- title:
--   Functions for the Fourier coefficient error assembly
-- statement:
--   The actual Gaussian zeta window, logarithmic Dirichlet weights and offsets, actual gamma moment Fourier samples and an explicit finite grouped sum. Functions only, with no enclosure, sign, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHHighBinningSemantic
import Definitions.Def_TaoFivePrimes_RHBatch01GlobalDirichletBins
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletArithmetic
open Complex
open scoped FourierTransform
namespace RHBatch01FullCoefficient
noncomputable def W (t : ℝ) : ℂ := completedRiemannZeta (1/2+((t+3289999808:ℝ):ℂ)*I)*
 Complex.exp (((Real.pi*(t+3289999808)/4-t^2/800:ℝ):ℂ))
noncomputable def L (n : Nat) : ℝ := Real.log (n:ℝ)+Real.log Real.pi/2
noncomputable def delta (n : Nat) : ℝ := 512*L n/(2*Real.pi)-(RHBatch01DirichletArithmetic.bin n:ℝ)
noncomputable def weight (n : Nat) : ℂ := Complex.exp (-(1/2+I*(3289999808:ℂ))*(L n:ℂ))
noncomputable def F (m b k : Nat) : ℂ := 𝓕 (RHHighSamplingFunctions.moment 3289999808 k) (((m+b:Nat):ℝ)/512)
noncomputable def group (G : Nat→Nat→ℂ) : ℂ :=
 ∑b:Fin 929,∑k:Fin 24,
 (RHHighBinningSemantic.pairValue (RHBatch01GlobalDirichletBins.coefficient b.val k.val)/(2:ℂ)^128)*G b.val k.val
end RHBatch01FullCoefficient
noncomputable def TaoFivePrimes_RHBatch01CoefficientFunctions : Nat := 24


