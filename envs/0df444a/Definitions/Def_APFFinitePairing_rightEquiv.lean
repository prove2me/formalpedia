-- Prove2me | Definitions.Def_APFFinitePairing_rightEquiv
-- name    : APFFinitePairing_rightEquiv
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-02T11:32:22.414862+00:00
-- url     : https://prove2.me/theorems/05f4f0e6-4d8a-4b8b-8e3a-b5294926b3d3
-- title:
--   Right quotient transport for equal tables
-- statement:
--   # Right quotient transport for equal tables
--
--   An equality of finite tables identifies their right radical quotient spaces by a real linear equivalence.
--
--   This is supporting mathematics at the exact stated hypotheses; it does not independently certify a physical realization of arbitrary model instances.
--
--   The real coefficient spaces are formal mathematical representations. This result does not assert physical mixing, a completed physical score, an identification of preparation and terminal roles, positive physical geometry, probability, or the Born rule.
-- source:
--   Accepted FinitePairing SHA 107c91c2303327b843165811135fc986989d73b36875cfe03f71638bf7b10cdc

import Definitions.Def_APFFinitePairing_RightSpace
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
def APFFinitePairing.rightEquiv (M N : I → J → ℝ) (h : M=N) : RightSpace M ≃ₗ[ℝ] RightSpace N := by
  subst N; exact LinearEquiv.refl ℝ _


