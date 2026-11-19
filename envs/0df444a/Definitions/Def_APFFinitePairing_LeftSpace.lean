-- Prove2me | Definitions.Def_APFFinitePairing_LeftSpace
-- name    : APFFinitePairing_LeftSpace
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-02T10:06:32.604529+00:00
-- url     : https://prove2.me/theorems/fb367686-5628-4fa9-8cf8-99426141e298
-- title:
--   Left quotient space
-- statement:
--   # Left quotient space
--
--   Quotient the formal row coefficient space by its left radical.
--
--   This is supporting mathematics at the exact stated hypotheses; it does not independently certify a physical realization of arbitrary model instances.
--
--   The real coefficient spaces are formal mathematical representations. This result does not assert physical mixing, a completed physical score, an identification of preparation and terminal roles, positive physical geometry, probability, or the Born rule.
-- source:
--   Accepted FinitePairing SHA 107c91c2303327b843165811135fc986989d73b36875cfe03f71638bf7b10cdc

import Definitions.Def_APFFinitePairing_LeftRad
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open APFFinitePairing
variable {I J : Type*} [Fintype I] [Fintype J]
abbrev APFFinitePairing.LeftSpace (M : I → J → ℝ) := (I → ℝ) ⧸ LeftRad M


