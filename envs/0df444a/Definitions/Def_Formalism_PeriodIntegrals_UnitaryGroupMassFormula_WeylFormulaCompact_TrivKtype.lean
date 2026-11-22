-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:33.009796+00:00
-- url     : https://prove2.me/theorems/f80fa618-7b0b-4b99-9332-7cc5a9429d10
-- title:
--   Triv Ktype
-- statement:
--   Definitions and structural lemmas for Triv Ktype, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/TrivKtype.lean

import Definitions.Def_Formalism_PeriodIntegrals_WeylForK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UpqRep Matrix
noncomputable section
namespace PI.WeylForKInhab
def triv (N : ℕ) : Matrix (Fin N) (Fin N) ℂ → (ℂ →L[ℂ] ℂ) := fun _ => 1
end PI.WeylForKInhab


