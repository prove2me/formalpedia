-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFiniteRank
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFiniteRank
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:55:21.845357+00:00
-- url     : https://prove2.me/theorems/1c213fab-d532-4d6a-918c-0023dcf0127f
-- title:
--   Statements Semilocal Finite Rank
-- statement:
--   Definitions and structural lemmas for Statements Semilocal Finite Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsSemilocalFiniteRank.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc
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
def SemilocalFiniteRank.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      Module.Finite (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) ∧
        Module.IsTorsionFree (degZeroLoc (contractPrime j P') {W})
          (degZeroLoc P' (fibrePrimes j P' W)) ∧
        Module.finrank (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) =
          relDeg j P'
end
end GroundTheory.Heights₂.Heights.FieldNumbers


