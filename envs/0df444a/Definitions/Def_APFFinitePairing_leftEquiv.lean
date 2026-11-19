-- Prove2me | Definitions.Def_APFFinitePairing_leftEquiv
-- name    : APFFinitePairing_leftEquiv
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-02T11:07:03.814882+00:00
-- url     : https://prove2.me/theorems/e5613c5c-99d7-44c8-96b5-0bd902f1a93b
-- title:
--   Left quotient transport for equal tables
-- statement:
--   # Left quotient transport for equal tables
--
--   An equality of finite tables identifies their left radical quotient spaces by a real linear equivalence.
--
--   This is supporting mathematics at the exact stated hypotheses; it does not independently certify a physical realization of arbitrary model instances.
--
--   The real coefficient spaces are formal mathematical representations. This result does not assert physical mixing, a completed physical score, an identification of preparation and terminal roles, positive physical geometry, probability, or the Born rule.
-- source:
--   Accepted FinitePairing SHA 107c91c2303327b843165811135fc986989d73b36875cfe03f71638bf7b10cdc

import Definitions.Def_APFFinitePairing_LeftRad
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
def APFFinitePairing.leftEquiv (M N : I → J → ℝ) (h : M=N) : LeftSpace M ≃ₗ[ℝ] LeftSpace N := by
  subst N; exact LinearEquiv.refl ℝ _


