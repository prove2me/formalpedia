-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ParamInjective
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ParamInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:31.078142+00:00
-- url     : https://prove2.me/theorems/24ccb191-4e76-4fcb-962a-c2a6270e4076
-- title:
--   Param Injective
-- statement:
--   Definitions and structural lemmas for Param Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ParamInjective.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
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
section C
variable {F : Type} [Field F] (O : Subring F) {ϖ : F} (hϖ : ϖ ∈ O)
def param {a t : ℕ} (J' : Subgroup (GL (Fin a) F)) (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a)
    (p : (redJ O ϖ hϖ J' hJ).range × Matrix (Fin a) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ×
      GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) :
    Matrix (Fin (a + t)) (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) :=
  theta ((p.1 : GL (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) : Matrix _ _ _) p.2.1 0
    ((p.2.2 : GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) : Matrix _ _ _)
end C
end PI.ParahoricIdxZ.W


