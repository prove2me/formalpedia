-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:14.416256+00:00
-- url     : https://prove2.me/theorems/f3186508-857c-54e8-8d53-e761963b7e0f
-- title:
--   Integrable Poly Gauss
-- statement:
--   Definitions and structural lemmas for Integrable Poly Gauss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_eq
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_zero
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_pow_quad
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_pk_deg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped FourierTransform
open MeasureTheory Complex MvPolynomial
namespace PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KLI (J pk J_eq J_zero intg_pow_quad pk_deg)
variable {ι : Type} [Fintype ι]
def phi (b : ℝ) (k : ℕ) (c : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ k * cexp ((-b : ℂ) * (x : ℂ) ^ 2 + c * x)
def kG (b : ℝ) : ℂ := ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ)
def linP (i : ι) (a : ℂ) (p : Polynomial ℂ) : MvPolynomial ι ℂ :=
  ∑ j ∈ Finset.range (p.natDegree + 1), C (p.coeff j * a ^ j) * X i ^ j
def rS (b : ℝ) (s : ι →₀ ℕ) : MvPolynomial ι ℂ :=
  C (kG b ^ Fintype.card ι) * ∏ i, linP i (2 * Real.pi * I) (pk (-b : ℂ) (s i))
end PositivityTheory.SiegelWeilFormula.KFPB
end


