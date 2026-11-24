-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:15.685549+00:00
-- url     : https://prove2.me/theorems/c8ac4872-8f72-4901-ab85-9b72db76da4b
-- title:
--   Second Minor Zero Level Formula
-- statement:
--   Definitions and structural lemmas for Second Minor Zero Level Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelIndex/SecondMinorZeroLevelFormula.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
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
namespace PI.QnZeroLevelWork
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
section Ops
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ}
def T1 (u : ℂ) (a β : Mx (k + 1) r → Fin (2 * r + k + 2) → ℂ) (f : Mx (k + 1) r → E) (g : Mx (k + 1) r)
    (i j : Fin (2 * r + k + 2)) : E :=
  ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * β g i * a g j) •
    qminorOp (EH (k + 1) r) (posL (k + 1) r 0 ∘ skip1 i) (posL (k + 1) r 0 ∘ skip1 j) u f g
def T2 (u : ℂ) (a a' β β' : Mx (k + 1) r → Fin (2 * r + k + 2) → ℂ) (f : Mx (k + 1) r → E)
    (g : Mx (k + 1) r) (i i' j j' : Fin (2 * r + k + 2)) : E :=
  ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (β g i * β' g i' - β g i' * β' g i) *
    (a g j * a' g j' - a g j' * a' g j)) •
    qminorOp (EH (k + 1) r) (posL (k + 1) r 0 ∘ skip2 i i') (posL (k + 1) r 0 ∘ skip2 j j') u f g
end Ops
end PI.QnZeroLevelWork


