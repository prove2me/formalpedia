-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:33:02.183657+00:00
-- url     : https://prove2.me/theorems/75a1b21b-4846-4b1a-b703-35184c16d2da
-- title:
--   Forward
-- statement:
--   Definitions and structural lemmas for Forward, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
def coefOf (b : Fin (r + 1)) (y : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) : ℂ :=
  if a = b then 1 else if h : a.val < b.val then y (eI k r ⟨a.val, by omega⟩) else 0
end PI.StabPairsW


