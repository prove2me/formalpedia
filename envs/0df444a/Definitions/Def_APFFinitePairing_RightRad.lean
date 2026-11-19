-- Prove2me | Definitions.Def_APFFinitePairing_RightRad
-- name    : APFFinitePairing_RightRad
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-02T10:03:56.880982+00:00
-- url     : https://prove2.me/theorems/d8d3162e-2b47-4038-b839-98596e8b7c1d
-- title:
--   Right radical
-- statement:
--   # Right radical
--
--   The right radical consists of column coefficients paired to zero with every row coefficient vector.
--
--   This is supporting mathematics at the exact stated hypotheses; it does not independently certify a physical realization of arbitrary model instances.
--
--   The real coefficient spaces are formal mathematical representations. This result does not assert physical mixing, a completed physical score, an identification of preparation and terminal roles, positive physical geometry, probability, or the Born rule.
-- source:
--   Accepted FinitePairing SHA 107c91c2303327b843165811135fc986989d73b36875cfe03f71638bf7b10cdc

import Definitions.Def_APFFinitePairing_form
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
abbrev APFFinitePairing.RightRad (M : I → J → ℝ) := (form M).flip.ker


