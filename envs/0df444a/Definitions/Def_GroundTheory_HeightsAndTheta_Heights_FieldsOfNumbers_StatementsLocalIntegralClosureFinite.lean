-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalIntegralClosureFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalIntegralClosureFinite
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:06:00.869926+00:00
-- url     : https://prove2.me/theorems/2c9964fb-3732-5fa6-87fd-a26a2fd5725e
-- title:
--   Statements Local Integral Closure Finite
-- statement:
--   Definitions and structural lemmas for Statements Local Integral Closure Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsLocalIntegralClosureFinite.lean

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
def LocalIntegralClosureFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P'), relDim (contractPrime j P') = relDim P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      ∃ s : Finset (FractionRing (MRing ι' F ⧸ P')),
        (∀ e ∈ s, e ∈ homFracDegZero P' ∧
          IsIntegral ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P')) e) ∧
        ∀ x ∈ homFracDegZero P',
          IsIntegral ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P')) x →
          x ∈ Submodule.span ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P'))
            (s : Set (FractionRing (MRing ι' F ⧸ P')))
end
end GroundTheory.Heights₂.Heights.FieldNumbers


