-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:19.606876+00:00
-- url     : https://prove2.me/theorems/7061332c-5627-4b0d-b2a8-7ea35826434e
-- title:
--   Hk Conj Transpose
-- statement:
--   Definitions and structural lemmas for Hk Conj Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/HkConjTranspose.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
def hkSig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩
def hkEps (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1
end AAInvW


