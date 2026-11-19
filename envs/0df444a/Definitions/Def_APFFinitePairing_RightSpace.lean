-- Prove2me | Definitions.Def_APFFinitePairing_RightSpace
-- name    : APFFinitePairing_RightSpace
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-02T11:04:43.38138+00:00
-- url     : https://prove2.me/theorems/b0863daa-fe60-41d3-a419-1aa2ec58f4f3
-- title:
--   Right quotient space
-- statement:
--   # Right quotient space
--
--   Quotient the formal column coefficient space by its right radical.
--
--   This is supporting mathematics at the exact stated hypotheses; it does not independently certify a physical realization of arbitrary model instances.
--
--   The real coefficient spaces are formal mathematical representations. This result does not assert physical mixing, a completed physical score, an identification of preparation and terminal roles, positive physical geometry, probability, or the Born rule.
-- source:
--   Accepted FinitePairing SHA 107c91c2303327b843165811135fc986989d73b36875cfe03f71638bf7b10cdc

import Definitions.Def_APFFinitePairing_RightRad
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open APFFinitePairing
variable {I J : Type*} [Fintype I] [Fintype J]
abbrev APFFinitePairing.RightSpace (M : I → J → ℝ) := (J → ℝ) ⧸ RightRad M


