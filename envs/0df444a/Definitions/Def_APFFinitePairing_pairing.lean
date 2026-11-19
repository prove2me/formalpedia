-- Prove2me | Definitions.Def_APFFinitePairing_pairing
-- name    : APFFinitePairing_pairing
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-02T11:32:12.320159+00:00
-- url     : https://prove2.me/theorems/2fb59f05-0059-4cda-aa99-ca16c4c01559
-- title:
--   Pairing on the two quotient spaces
-- statement:
--   # Pairing on the two quotient spaces
--
--   The table form descends to the left and right radical quotients.
--
--   This is supporting mathematics at the exact stated hypotheses; it does not independently certify a physical realization of arbitrary model instances.
--
--   The real coefficient spaces are formal mathematical representations. This result does not assert physical mixing, a completed physical score, an identification of preparation and terminal roles, positive physical geometry, probability, or the Born rule.
-- source:
--   Accepted FinitePairing SHA 107c91c2303327b843165811135fc986989d73b36875cfe03f71638bf7b10cdc

import Definitions.Def_APFFinitePairing_LeftRad
import Definitions.Def_APFFinitePairing_RightRad
import Definitions.Def_APFFinitePairing_RightSpace
import Definitions.Def_APFFinitePairing_form
import Definitions.Def_APFFinitePairing_LeftSpace
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open APFFinitePairing
variable {I J : Type*} [Fintype I] [Fintype J]
def APFFinitePairing.pairing (M : I → J → ℝ) : LeftSpace M →ₗ[ℝ] RightSpace M →ₗ[ℝ] ℝ :=
  (form M).liftQ₂ (LeftRad M) (RightRad M) le_rfl le_rfl


