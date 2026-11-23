-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_HvScalar
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_HvScalar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:18.362987+00:00
-- url     : https://prove2.me/theorems/622dfd52-aba9-4869-8f4c-a93a7829032e
-- title:
--   Hv Scalar
-- statement:
--   Definitions and structural lemmas for Hv Scalar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HvScalar.lean

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
open Matrix Classical
namespace PI.IsoInvMetricW
open PI.IsoInvMetric
def dg {Lt : Type} {N : ℕ} (w : Lt → Fin N → ℕ → ℂ) (s : Lt) (i : ℕ) : ℂ :=
  if h : i < N then w s ⟨i, h⟩ i else 0
end PI.IsoInvMetricW


