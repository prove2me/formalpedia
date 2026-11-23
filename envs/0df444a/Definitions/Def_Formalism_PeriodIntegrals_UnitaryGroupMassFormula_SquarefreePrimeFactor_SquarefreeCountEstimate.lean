-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:58:16.456294+00:00
-- url     : https://prove2.me/theorems/7d63aa50-8156-4a9a-a21d-349573f7807d
-- title:
--   Squarefree Count Estimate
-- statement:
--   Definitions and structural lemmas for Squarefree Count Estimate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/SquarefreeCountEstimate.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
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
namespace PI.SqfPrimeFactor.W
open PI.SqfLab
def bad (g r p : ℕ) [Fact g.Prime] : Finset (ZMod g)[X] :=
  (irrDeg g p ×ˢ monicDeg g (r - p)).image (fun x => x.1 * x.2)
section
variable {g : ℕ} [Fact g.Prime]
end
end PI.SqfPrimeFactor.W


