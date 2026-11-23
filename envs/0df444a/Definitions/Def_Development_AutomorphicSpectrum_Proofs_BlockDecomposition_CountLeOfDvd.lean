-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:20.018413+00:00
-- url     : https://prove2.me/theorems/c5a5789c-9f92-4d12-9655-fc21cdf1706d
-- title:
--   Count Le Of Dvd
-- statement:
--   Definitions and structural lemmas for Count Le Of Dvd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountLeOfDvd.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
namespace GlobalTheory.CompanionTheory.GapPolyProof
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
def dd (n : ℕ) (v : ℕ → E) (ψ : E →ₗ[ℂ] ℂ) : ℂ[X] :=
  ∑ j ∈ Finset.range (n + 1), C (ψ (v j)) * X ^ (n - j)
end GlobalTheory.CompanionTheory.GapPolyProof


