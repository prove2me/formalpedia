-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSup
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSup
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:08:06.218155+00:00
-- url     : https://prove2.me/theorems/2f06485e-f0e5-47a8-9097-816f523dcfc2
-- title:
--   Minimal Primes Of Multihomog Sup
-- statement:
--   Definitions and structural lemmas for Minimal Primes Of Multihomog Sup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MinimalPrimesOfMultihomogSup.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.MinHom
open MvPolynomial ReciprocityTheory.AnForm.R
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end GlobalTheory.CompanionTheory.Ar.Cmp.MinHom


