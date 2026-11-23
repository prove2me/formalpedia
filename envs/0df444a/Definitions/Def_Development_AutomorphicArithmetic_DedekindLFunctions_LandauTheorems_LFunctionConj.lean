-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
-- name    : Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:12.625794+00:00
-- url     : https://prove2.me/theorems/a221dffc-d542-4a30-bf8a-9dedb2b2df5e
-- title:
--   LFunction Conj
-- statement:
--   Definitions and structural lemmas for LFunction Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LFunctionConj.lean

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Deduction
namespace LFunctionConjugation
open HurwitzZeta
def reg (a : UnitAddCircle) (s : ℂ) : ℂ := hurwitzZeta a s - 1 / (s - 1) / Gammaℝ s
end LFunctionConjugation
end Deduction
end


