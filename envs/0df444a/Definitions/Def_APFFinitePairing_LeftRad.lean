-- Prove2me | Definitions.Def_APFFinitePairing_LeftRad
-- name    : APFFinitePairing_LeftRad
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-02T08:32:16.395224+00:00
-- url     : https://prove2.me/theorems/10e12da5-8582-41bc-99b8-c5c12d1d9b90
-- title:
--   Left radical
-- statement:
--   # Left radical
--
--   The left radical consists of row coefficients paired to zero with every column coefficient vector.
--
--   This is supporting mathematics at the exact stated hypotheses; it does not independently certify a physical realization of arbitrary model instances.
--
--   The real coefficient spaces are formal mathematical representations. This result does not assert physical mixing, a completed physical score, an identification of preparation and terminal roles, positive physical geometry, probability, or the Born rule.
-- source:
--   Accepted FinitePairing SHA 107c91c2303327b843165811135fc986989d73b36875cfe03f71638bf7b10cdc

import Definitions.Def_APFFinitePairing_form
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open APFFinitePairing
variable {I J : Type*} [Fintype I] [Fintype J]
abbrev APFFinitePairing.LeftRad (M : I → J → ℝ) := (form M).ker


