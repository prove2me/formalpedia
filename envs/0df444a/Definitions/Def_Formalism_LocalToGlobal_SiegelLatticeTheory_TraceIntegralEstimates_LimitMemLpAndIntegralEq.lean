-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:56.339058+00:00
-- url     : https://prove2.me/theorems/d96ba40d-61ba-42c8-81c4-3cd3e2fbe398
-- title:
--   Limit Mem Lp And Integral Eq
-- statement:
--   Definitions and structural lemmas for Limit Mem Lp And Integral Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/LimitMemLpAndIntegralEq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate
namespace Formalism.L2.S.Pv.SchurTens
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
end Formalism.L2.S.Pv.SchurTens


