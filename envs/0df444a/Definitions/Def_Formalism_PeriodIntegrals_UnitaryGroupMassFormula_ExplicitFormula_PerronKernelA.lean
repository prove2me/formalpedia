-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:14.072085+00:00
-- url     : https://prove2.me/theorems/b830c9b3-ed0a-4334-87c7-31e6fca5126f
-- title:
--   Perron Kernel A
-- statement:
--   Definitions and structural lemmas for Perron Kernel A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
noncomputable def ker (l : ℝ) (s : ℂ) : ℂ := cexp (l * s) / s
noncomputable def gl (l : ℝ) : ℂ → ℂ := dslope (fun s : ℂ => cexp (l * s)) 0
end PI.EF.PK


