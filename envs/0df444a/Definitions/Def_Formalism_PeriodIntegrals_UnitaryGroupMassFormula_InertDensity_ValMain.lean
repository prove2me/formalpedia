-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:20:32.544498+00:00
-- url     : https://prove2.me/theorems/2a6e5543-a13c-4a69-869d-e1e33ad262fd
-- title:
--   Val Main
-- statement:
--   Definitions and structural lemmas for Val Main, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ValMain.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
namespace DensInertW
section
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L] {n : ℕ}
  {M : Matrix (Fin n) (Fin n) L}
end
end DensInertW


