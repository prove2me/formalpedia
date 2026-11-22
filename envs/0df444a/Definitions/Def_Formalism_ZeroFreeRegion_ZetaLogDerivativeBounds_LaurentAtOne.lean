-- Prove2me | Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LaurentAtOne
-- name    : Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LaurentAtOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:29.39125+00:00
-- url     : https://prove2.me/theorems/90de0edc-3e62-4bf4-b75a-871e2871cd08
-- title:
--   Laurent At One
-- statement:
--   Definitions and structural lemmas for Laurent At One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LaurentAtOne.lean

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
namespace Formalism.ZF
def laHfun (y : ℝ) (s : ℂ) : ℂ :=
  (1 - (s - 1) * (deriv riemannZeta₁ s / riemannZeta₁ s)) * ((y : ℂ) ^ s / s)
def laU : Set ℂ := {s | riemannZeta₁ s ≠ 0} ∩ {s | s ≠ 0}
end Formalism.ZF


