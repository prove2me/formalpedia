-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreRelDim
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreRelDim
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:06:45.655522+00:00
-- url     : https://prove2.me/theorems/35e55e56-4b56-4241-9b8c-e73817a4783e
-- title:
--   Statements Fibre Rel Dim
-- statement:
--   Definitions and structural lemmas for Statements Fibre Rel Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsFibreRelDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFiniteRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
def FibreRelDim.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ n : ℕ, relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → ∀ W' ∈ fibrePrimes j P' W, relDim W' = (n : ℕ)
end
end GroundTheory.Heights₂.Heights.FieldNumbers


