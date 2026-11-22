-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:46:20.648345+00:00
-- url     : https://prove2.me/theorems/26ba4492-2495-4ec4-8ca3-25a4a830f6e5
-- title:
--   ZIter A
-- statement:
--   Definitions and structural lemmas for ZIter A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
section quad
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
end quad
section words
variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]
end words
end PI.UnitaryGroupMassFormula.UsCost.ZI


