-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChart
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChart
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:18:26.765455+00:00
-- url     : https://prove2.me/theorems/599c7c46-42b6-474c-b5e2-6d73625991c8
-- title:
--   Symbolic Power In Affine Chart
-- statement:
--   Definitions and structural lemmas for Symbolic Power In Affine Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerInAffineChart.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def chartSub {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L) :
    MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ →ₐ[ℂ] L :=
  aeval fun j => w ((Fintype.equivFin (Σ k, ι k)).symm j)
variable {L : Type} [CommRing L] [Algebra ℂ L] [Algebra (MvPolynomial (Σ k, ι k) ℂ) L]
  [IsScalarTower ℂ (MvPolynomial (Σ k, ι k) ℂ) L]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog


