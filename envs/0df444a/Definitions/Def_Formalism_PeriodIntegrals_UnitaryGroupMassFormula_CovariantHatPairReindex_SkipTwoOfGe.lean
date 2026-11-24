-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:36.135637+00:00
-- url     : https://prove2.me/theorems/59c251d0-35ae-48ee-9ac6-603b94fd8193
-- title:
--   Skip Two Of Ge
-- statement:
--   Definitions and structural lemmas for Skip Two Of Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean

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
namespace PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
noncomputable def sgnL {r : ℕ} {α : Type*} [DecidableEq α] (x e : Fin r → α) : ℂ :=
  Matrix.det (Matrix.of fun k j => if x k = e j then (1 : ℂ) else 0)
end PI.QnCovHat2W


