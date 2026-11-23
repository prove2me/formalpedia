-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_RepCountCongruenceInvariant
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_RepCountCongruenceInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:51.350333+00:00
-- url     : https://prove2.me/theorems/b4587229-9f6b-4122-a932-62b2d77aa9dc
-- title:
--   Rep Count Congruence Invariant
-- statement:
--   Definitions and structural lemmas for Rep Count Congruence Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/RepCountCongruenceInvariant.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace DensInertW
def cgComb {L : Type} [Field L] {m n : ℕ} (Q : Matrix (Fin m) (Fin m) L) (X : Fin m → Fin n → L) :
    Fin m → Fin n → L :=
  fun i => ∑ k, Q i k • X k
end DensInertW


