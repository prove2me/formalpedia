-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_GoodRDeltaB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_GoodRDeltaB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:17:31.180076+00:00
-- url     : https://prove2.me/theorems/a313df26-6d45-4680-b3c4-c9af56e7fb31
-- title:
--   Good RDelta B
-- statement:
--   Definitions and structural lemmas for Good RDelta B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/GoodRDeltaB.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.CntFormula.DeltaB
open Polynomial
variable {R K A : Type} [CommRing R] [Field K] [CommRing A] [Algebra R K] [Algebra K A] [Algebra R A]
  [IsScalarTower R K A]
end PI.UnitaryGroupMassFormula.CntFormula.DeltaB


