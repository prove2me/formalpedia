-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:44:55.854622+00:00
-- url     : https://prove2.me/theorems/d484e11c-f7db-44f7-80f2-b8e111fdc6a8
-- title:
--   Nilpotent Orthogonal Complement
-- statement:
--   Definitions and structural lemmas for Nilpotent Orthogonal Complement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
namespace PI.StabSplit.UnipW
def perpX (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ i : Fin (2 * r + k + 1), r + k < i.val → v i = 0
def inX (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0
def Lk (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩
end PI.StabSplit.UnipW
namespace PI.StabSplit
end PI.StabSplit


