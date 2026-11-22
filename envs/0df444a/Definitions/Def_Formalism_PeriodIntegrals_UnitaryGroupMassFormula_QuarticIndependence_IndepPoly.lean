-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepPoly
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepPoly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:41:13.60643+00:00
-- url     : https://prove2.me/theorems/ed7f856d-5e68-439a-897b-f6733ab4f7b3
-- title:
--   Indep Poly
-- statement:
--   Definitions and structural lemmas for Indep Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuarticIndependence/IndepPoly.lean

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
def IndepPoly : Prop :=
  ∀ Y Y' : ℂ, Y' ≠ Y + 1 → ∀ z : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℂ,
    (∀ β α : ℂ, (∃ n : ℤ, α = β + n) →
      (Y - β) * (Y' - β) * ((Y' + α) * (Y + α)) * z (0, 0) (0, 0) = 0 ∧
      (Y - β) * (Y' - β) * ((Y' + α - 1) * z (0, 0) (0, 1) + (Y + α) * z (0, 0) (1, 0)) = 0 ∧
      (Y - β) * (Y' - β) * z (0, 0) (1, 1) = 0 ∧
      ((Y' - β) * z (0, 1) (0, 0) + (Y - β + 1) * z (1, 0) (0, 0)) * ((Y' + α) * (Y + α)) = 0 ∧
      (Y' - β) * (Y' + α - 1) * z (0, 1) (0, 1) + (Y' - β) * (Y + α) * z (0, 1) (1, 0) +
          (Y - β + 1) * (Y' + α - 1) * z (1, 0) (0, 1) + (Y - β + 1) * (Y + α) * z (1, 0) (1, 0) = 0 ∧
      (Y' - β) * z (0, 1) (1, 1) + (Y - β + 1) * z (1, 0) (1, 1) = 0 ∧
      (Y' + α) * (Y + α) * z (1, 1) (0, 0) = 0 ∧
      (Y' + α - 1) * z (1, 1) (0, 1) + (Y + α) * z (1, 1) (1, 0) = 0 ∧
      z (1, 1) (1, 1) = 0) →
    ∀ A B, z A B = 0
end PI.QmIndepW


