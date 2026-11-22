-- Prove2me | Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
-- name    : Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:41.798089+00:00
-- url     : https://prove2.me/theorems/84ccb114-61fa-4ee0-a637-d0bd2cb1a1f1
-- title:
--   Norm Cpow Sub Le Point
-- statement:
--   Definitions and structural lemmas for Norm Cpow Sub Le Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormCpowSubLePoint.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
namespace Formalism.ZF
namespace ComplexPowerDifferenceIntegral
def eint (s : ℂ) (a : ℝ) : ℂ := ∫ x in a..(a + 1), ((x : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s))
end ComplexPowerDifferenceIntegral
end Formalism.ZF


