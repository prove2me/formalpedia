-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConvAlg
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConvAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:07:36.08887+00:00
-- url     : https://prove2.me/theorems/600f28f3-0098-4288-b594-cdf9f1bb6b9e
-- title:
--   Conv Alg
-- statement:
--   Definitions and structural lemmas for Conv Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/ConvAlg.lean

import Mathlib
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
namespace PI.StabPairs.ConvAlg
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
def rhoOf (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ) : Matrix n n ℂ :=
  1 + F * ((W - 1) * ((Fᴴ * H * F)⁻¹ * (Fᴴ * H)))
end PI.StabPairs.ConvAlg


