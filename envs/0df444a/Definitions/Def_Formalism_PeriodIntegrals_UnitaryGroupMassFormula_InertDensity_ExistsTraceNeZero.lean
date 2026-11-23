-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:26.495465+00:00
-- url     : https://prove2.me/theorems/5697fd77-78e5-417b-b3c1-3a044081b79a
-- title:
--   Exists Trace Ne Zero
-- statement:
--   Definitions and structural lemmas for Exists Trace Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ExistsTraceNeZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
namespace DensInertW
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable (K) in

def conj : L →+* L := (FiniteField.frobeniusAlgHom K L).toRingHom
end DensInertW


