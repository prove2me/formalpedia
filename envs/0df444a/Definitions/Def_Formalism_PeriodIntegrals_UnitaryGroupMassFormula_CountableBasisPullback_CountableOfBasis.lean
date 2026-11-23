-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountableBasisPullback_CountableOfBasis
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountableBasisPullback_CountableOfBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:38.218513+00:00
-- url     : https://prove2.me/theorems/e29d37e9-6891-43ca-af3e-f8febf636157
-- title:
--   Countable Of Basis
-- statement:
--   Definitions and structural lemmas for Countable Of Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountableBasisPullback/CountableOfBasis.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NormPullG
import Definitions.Def_Formalism_PeriodIntegrals_HeisPull
import Definitions.Def_Formalism_PeriodIntegrals_HeisNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace PI.NormPullGW
variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]
instance haarIJ : (volume : Measure (I → J → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : I => (volume : Measure (J → ℂ)))
instance haarTIJ : (volume : Measure (T → I → J → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : T => (volume : Measure (I → J → ℂ)))
noncomputable def phi (A : ℝ) (F : (T → I → J → ℂ) → ℂ) (z : T → I → J → ℂ) : ℝ :=
  ‖F z‖ ^ 2 * Real.exp (-Real.pi * (HfG A z z).re)
end PI.NormPullGW


