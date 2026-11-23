-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:13.425732+00:00
-- url     : https://prove2.me/theorems/1c98bdb3-087b-4dc3-941c-71ccd23c9784
-- title:
--   Monic Deg Fn Nat Degree
-- statement:
--   Definitions and structural lemmas for Monic Deg Fn Nat Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/MonicDegFnNatDegree.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
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
variable {g : ℕ} [Fact g.Prime]
end PI.SqfPrimeFactor.W


