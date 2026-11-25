-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:07:19.264497+00:00
-- url     : https://prove2.me/theorems/8f7ec3c2-955c-425e-a899-01ed5521cd93
-- title:
--   Affine Chart Ideal Prime And Saturated
-- statement:
--   Definitions and structural lemmas for Affine Chart Ideal Prime And Saturated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AffineChartIdealPrimeAndSaturated.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def phi (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime] :
    MvPolynomial (Σ k, ι k) ℂ →+* FractionRing (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) :=
  (algebraMap (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) _).comp (Ideal.Quotient.mk Q)
def theta (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime] (p : (k : K) → ι k) :
    MvPolynomial (Σ k, ι k) ℂ →+* FractionRing (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) :=
  eval₂Hom ((phi Q).comp C) (fun q => phi Q (X q) / phi Q (X ⟨q.1, p q.1⟩))
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict


