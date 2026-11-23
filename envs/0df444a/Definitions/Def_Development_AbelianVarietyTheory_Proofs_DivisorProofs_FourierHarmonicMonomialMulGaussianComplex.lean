-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierHarmonicMonomialMulGaussianComplex
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierHarmonicMonomialMulGaussianComplex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:11.059734+00:00
-- url     : https://prove2.me/theorems/c453d921-af7a-4928-bdf6-7d0ff1e125f3
-- title:
--   Fourier Harmonic Monomial Mul Gaussian Complex
-- statement:
--   Definitions and structural lemmas for Fourier Harmonic Monomial Mul Gaussian Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierHarmonicMonomialMulGaussianComplex.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
namespace GlobalTheory.HeckeLemma
def lin (a b w : ℂ) : ℂ := a * (w.re : ℂ) + b * (w.im : ℂ)
def ker (l w : ℂ) : ℂ :=
  Complex.exp (-2 * Real.pi * ((w.re : ℂ) ^ 2 + (w.im : ℂ) ^ 2)
    - 2 * Real.pi * Complex.I * ((w.re : ℂ) * l.re + (w.im : ℂ) * l.im))
end GlobalTheory.HeckeLemma


