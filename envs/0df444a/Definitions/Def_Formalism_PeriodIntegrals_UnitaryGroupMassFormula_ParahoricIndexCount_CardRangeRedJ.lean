-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:04.824794+00:00
-- url     : https://prove2.me/theorems/510fbb4a-6cd3-4e87-9021-0e08dbc8dfb2
-- title:
--   Card Range Red J
-- statement:
--   Definitions and structural lemmas for Card Range Red J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/CardRangeRedJ.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures.P.GLRed
namespace PI.ParahoricIdxZ.W
section B
variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)
def redJ {a : ℕ} (J' : Subgroup (GL (Fin a) F)) (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) :
    J' →* GL (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) :=
  (red O a ϖ hϖ).comp (Subgroup.inclusion hJ)
end B
end PI.ParahoricIdxZ.W


