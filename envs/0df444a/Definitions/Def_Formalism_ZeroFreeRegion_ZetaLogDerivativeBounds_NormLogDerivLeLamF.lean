-- Prove2me | Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormLogDerivLeLamF
-- name    : Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormLogDerivLeLamF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:48.054358+00:00
-- url     : https://prove2.me/theorems/8b650b2f-500d-463b-8593-afdf89cdf7e8
-- title:
--   Norm Log Deriv Le Lam F
-- statement:
--   Definitions and structural lemmas for Norm Log Deriv Le Lam F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormLogDerivLeLamF.lean

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation
noncomputable section
namespace Formalism.ZF
def lamF (σ : ℝ) : ℝ := ∑' n, ‖term ↗Λ (σ : ℂ) n‖
end Formalism.ZF


