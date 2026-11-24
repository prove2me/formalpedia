-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:45:04.746974+00:00
-- url     : https://prove2.me/theorems/91340586-6267-402c-81fd-b2c9c46d7428
-- title:
--   PRow WSCol W
-- statement:
--   Definitions and structural lemmas for PRow WSCol W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Formalism.QuantumDeterminants
noncomputable section
namespace NFOne
def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
def dW (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1
def Pm (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun p q =>
  if p.val < r then
    (if r ≤ q.val ∧ q.val ≤ r + k then -(dW k r q * star (V p.val q))
     else if r + k < q.val then
       (if (sg k r q).val < j then V (sg k r q).val p else -star (V p.val (sg k r q)))
     else 0)
  else if r ≤ p.val ∧ p.val ≤ r + k then
    (if r + k < q.val then V (sg k r q).val p else 0)
  else 0
end NFOne


