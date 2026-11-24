-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:06.299902+00:00
-- url     : https://prove2.me/theorems/4bcac324-0903-4691-8382-bf247a337dd5
-- title:
--   Coinv Reduction
-- statement:
--   Definitions and structural lemmas for Coinv Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms.Coinv
open MvPolynomial Finset
noncomputable section
variable (K : Type*) [Field K] (f n : ℕ)
def bps (m : ℕ) (b : Fin f) : MvPolynomial (Fin f × Fin n) K := ∑ i : Fin n, X (b, i) ^ m
def psumIdeal : Ideal (MvPolynomial (Fin f × Fin n) K) :=
  Ideal.span {P | ∃ m b, 1 ≤ m ∧ m ≤ n ∧ P = bps K f n m b}
variable {K f n}
variable [CharZero K]
end
end GroundTheory.Heights₂.Heights.RestTerms.Coinv


