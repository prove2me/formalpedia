-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T15:11:01.384818+00:00
-- url     : https://prove2.me/theorems/5b62e9be-c3d7-4824-a48e-119f69f320ed
-- title:
--   Is Unit Det Of Mem GV
-- statement:
--   Definitions and structural lemmas for Is Unit Det Of Mem GV, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
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
def sgI (k r : ℕ) (i : ℕ) : ℕ := if i < r ∨ r + k < i then 2 * r + k - i else i
lemma sgI_lt (i : Fin (2 * r + k + 1)) : sgI k r i.val < 2 * r + k + 1 := by
  have hi := i.isLt
  unfold sgI
  split_ifs <;> omega
def Ff (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i a => fvec k r z a i
end PI.StabPairsW


