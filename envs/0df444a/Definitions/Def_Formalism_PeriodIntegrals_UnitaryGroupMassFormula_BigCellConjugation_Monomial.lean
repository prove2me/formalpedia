-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BigCellConjugation_Monomial
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BigCellConjugation_Monomial
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:01:38.849672+00:00
-- url     : https://prove2.me/theorems/009241f6-b340-4cc8-b5ab-06d83072946f
-- title:
--   Monomial
-- statement:
--   Definitions and structural lemmas for Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BigCellConjugation/Monomial.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.SwBig.BigCellGProof
open PI.SwBig
def rhoB (k r : ℕ) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if j.val < r ∨ r + k < j.val then ⟨2 * r + k - j.val, by omega⟩ else j
end PI.SwBig.BigCellGProof


