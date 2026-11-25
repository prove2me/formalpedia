-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocDim
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocDim
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:05:27.52509+00:00
-- url     : https://prove2.me/theorems/a26af5ad-5c93-57a4-90c4-f1705321a2a2
-- title:
--   Statements Deg Zero Loc Dim
-- statement:
--   Definitions and structural lemmas for Statements Deg Zero Loc Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLocDim.lean

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
def DegZeroLocDim.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)), IsMultiProjPrime W → P ≤ W →
    haveI := hP.isPrime
    ringKrullDim (degZeroLoc P {W}) + ringKrullDim (MRing ι F ⧸ W) = ringKrullDim (MRing ι F ⧸ P)
end
end GroundTheory.Heights₂.Heights.FieldNumbers


