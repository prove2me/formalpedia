-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_EvalXAddCMul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_EvalXAddCMul
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:23:20.808401+00:00
-- url     : https://prove2.me/theorems/db015ceb-f9fa-43a9-97b0-b4ece3d0679f
-- title:
--   Eval XAdd CMul
-- statement:
--   Definitions and structural lemmas for Eval XAdd CMul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonicShiftEvaluation/EvalXAddCMul.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
open Formalism.QuantumDeterminants
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
abbrev R (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] := Module.End ℂ (WSm r E)
def PQ (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] : ℕ → (R r E)[X] × (R r E)[X]
  | 0 => (1, 0)
  | i + 1 =>
    if h : i < r then
      ((X + C (pEnd ⟨i, h⟩)) * (PQ r E i).1 - C (cEnd ⟨i, h⟩) * (PQ r E i).2,
        C (ciEnd ⟨i, h⟩) * (PQ r E i).1)
    else PQ r E i
end Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation


