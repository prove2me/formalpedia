-- Prove2me | Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
-- name    : Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:15:00.213814+00:00
-- url     : https://prove2.me/theorems/f8c2134b-60dd-42d3-83f8-dbc8c811b3ae
-- title:
--   Dz Differentiable On
-- statement:
--   Definitions and structural lemmas for Dz Differentiable On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/DzDifferentiableOn.lean

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
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
def dz (s : ℂ) (n : ℕ) : ℂ :=
  (((n : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) - ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (1 - s) -
    (s - 1) * ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s)
def Dz (s : ℂ) : ℂ := ∑' n, dz s n
end ComplexPowerDifferenceIntegral
end Formalism.ZF


