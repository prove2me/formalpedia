-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitGen
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitGen
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:11.215567+00:00
-- url     : https://prove2.me/theorems/73eac3e0-3326-4e60-aa7c-29993fcd7d63
-- title:
--   Split Gen
-- statement:
--   Definitions and structural lemmas for Split Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SplitGen.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
end PI.UnitaryGroupMassFormula.ScXuExists


