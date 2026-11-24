-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:43:26.872818+00:00
-- url     : https://prove2.me/theorems/bfb95fca-2f56-4f1a-b50d-66f6b75547f4
-- title:
--   Kronecker Real
-- statement:
--   Definitions and structural lemmas for Kronecker Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/KroneckerReal.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open Formalism.HermitianLattices.GL2PrimeSums
namespace GlobalTheory.TailIntegralOfSummatory
noncomputable def recSum (a : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ Icc 1 N, a n / (n : ℂ)
end GlobalTheory.TailIntegralOfSummatory


