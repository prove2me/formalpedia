-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Weights
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Weights
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:23.501412+00:00
-- url     : https://prove2.me/theorems/766fef26-0584-4e19-bb0a-21973b0f4bdd
-- title:
--   Weights
-- statement:
--   Definitions and structural lemmas for Weights, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Weights.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
import Definitions.Def_Lemmata_GeneralBFactLeftVariant_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WeylForKWork
open PI PI.UpqRep Matrix
open scoped InnerProductSpace
def wtTorus {N : ℕ} (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)
end PI.WeylForKWork


