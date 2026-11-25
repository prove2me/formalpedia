-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:16:32.018602+00:00
-- url     : https://prove2.me/theorems/1d00c842-671f-46ac-ba8d-9724b26dc9be
-- title:
--   Statements Function Field Finite
-- statement:
--   Definitions and structural lemmas for Statements Function Field Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsFunctionFieldFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalIntegralClosureFinite
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
def FunctionFieldFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P'), relDim (contractPrime j P') = relDim P' →
      haveI := hP'.isPrime
      relDeg j P' ≠ 0
end
end GroundTheory.Heights₂.Heights.FieldNumbers


