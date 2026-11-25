-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocLocal
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:05:45.948805+00:00
-- url     : https://prove2.me/theorems/57346a95-a5a1-4497-b37c-dbc6dbb3c189
-- title:
--   Statements Deg Zero Loc Local
-- statement:
--   Definitions and structural lemmas for Statements Deg Zero Loc Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLocLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocalRing
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
def DegZeroLocLocal.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)), IsMultiProjPrime W → P ≤ W →
    haveI := hP.isPrime
    IsLocalRing (degZeroLoc P {W})
end
end GroundTheory.Heights₂.Heights.FieldNumbers


