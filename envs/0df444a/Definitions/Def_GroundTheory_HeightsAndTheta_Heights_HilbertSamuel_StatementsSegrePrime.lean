-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegrePrime
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegrePrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:50.097387+00:00
-- url     : https://prove2.me/theorems/ad965df0-a4fe-49ff-a1da-6fafbd68d916
-- title:
--   Statements Segre Prime
-- statement:
--   Definitions and structural lemmas for Statements Segre Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsSegrePrime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
def SegrePrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    IsMultiProjPrime (segrePrime F q)
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


