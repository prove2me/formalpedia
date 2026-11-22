-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:39:18.802726+00:00
-- url     : https://prove2.me/theorems/c9c0ef9b-b039-4824-b80d-d8b551e16808
-- title:
--   Indep C
-- statement:
--   Definitions and structural lemmas for Indep C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuarticIndependence/IndepC.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.QmIndepW
open Complex
def nine (u v y00 y10 y20 y01 y11 y21 y02 y12 y22 : ℂ) : ℂ :=
  y00 + u * y10 + u ^ 2 * y20 + v * y01 + u * v * y11 + u ^ 2 * v * y21 + v ^ 2 * y02 + u * v ^ 2 * y12 +
    u ^ 2 * v ^ 2 * y22
def IndepC : Prop :=
  ∀ y00 y10 y20 y01 y11 y21 y02 y12 y22 : ℂ,
    (∀ c : ℂ, c ≠ 0 → nine c⁻¹ (star c)⁻¹ y00 y10 y20 y01 y11 y21 y02 y12 y22 = 0) →
    y00 = 0 ∧ y10 = 0 ∧ y20 = 0 ∧ y01 = 0 ∧ y11 = 0 ∧ y21 = 0 ∧ y02 = 0 ∧ y12 = 0 ∧ y22 = 0
end PI.QmIndepW


