-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSpans_SpanPowSmul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSpans_SpanPowSmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:00.910787+00:00
-- url     : https://prove2.me/theorems/a1b85608-9120-41a4-9f2c-108d73c69afe
-- title:
--   Span Pow Smul
-- statement:
--   Definitions and structural lemmas for Span Pow Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSpans/SpanPowSmul.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.ProjCW
open Formalism.BasicNotions NumberField IsDedekindDomain
section General
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end General
end PI.Dv.ProjCW


