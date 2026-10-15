-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighCoefficientFunctions
-- name    : TaoFivePrimes_RHHighCoefficientFunctions
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T08:59:27.56416+00:00
-- url     : https://prove2.me/theorems/59f11080-e953-4d9d-bc45-cfcd446f3f4e
-- title:
--   Functions for the Fourier coefficient error assembly
-- statement:
--   The actual Gaussian zeta window, logarithmic Dirichlet weights and offsets, actual gamma moment Fourier samples and an explicit finite grouped sum. Functions only, with no enclosure, sign, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHHighBinningSemantic
import Definitions.Def_TaoFivePrimes_RHHighGlobalDirichletBins
import Definitions.Def_TaoFivePrimes_RHHighDirichletArithmetic
open Complex
open scoped FourierTransform
namespace RHHighFullCoefficient
noncomputable def W (t : ℝ) : ℂ := completedRiemannZeta (1/2+((t+3289999936:ℝ):ℂ)*I)*
 Complex.exp (((Real.pi*(t+3289999936)/4-t^2/800:ℝ):ℂ))
noncomputable def L (n : Nat) : ℝ := Real.log (n:ℝ)+Real.log Real.pi/2
noncomputable def delta (n : Nat) : ℝ := 512*L n/(2*Real.pi)-(RHHighDirichletArithmetic.bin n:ℝ)
noncomputable def weight (n : Nat) : ℂ := Complex.exp (-(1/2+I*(3289999936:ℂ))*(L n:ℂ))
noncomputable def F (m b k : Nat) : ℂ := 𝓕 (RHHighSamplingFunctions.moment 3289999936 k) (((m+b:Nat):ℝ)/512)
noncomputable def group (G : Nat→Nat→ℂ) : ℂ :=
 ∑b:Fin 929,∑k:Fin 24,
 (RHHighBinningSemantic.pairValue (RHHighGlobalDirichletBins.coefficient b.val k.val)/(2:ℂ)^128)*G b.val k.val
end RHHighFullCoefficient
noncomputable def TaoFivePrimes_RHHighCoefficientFunctions : Nat := 24


