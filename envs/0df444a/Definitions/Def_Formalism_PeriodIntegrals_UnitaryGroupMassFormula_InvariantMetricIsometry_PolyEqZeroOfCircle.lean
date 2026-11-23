-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:02.458841+00:00
-- url     : https://prove2.me/theorems/e4a72127-aea3-4cb7-88ac-b79390822c8b
-- title:
--   Poly Eq Zero Of Circle
-- statement:
--   Definitions and structural lemmas for Poly Eq Zero Of Circle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical Finset PI.IsoInvMetric Polynomial
namespace PI.IsoInvMetricW
section
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
def wt (J : ColChoice N nu) : ℕ := ∑ s, ∑ c, ∑ i, (N - ((J s c i : Fin N) : ℕ))
def dz (z : ℂ) (_s : Lt) (a : Fin N) : ℂ := z ^ (N - (a : ℕ))
end
end PI.IsoInvMetricW


