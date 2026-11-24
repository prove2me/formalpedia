-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EisensteinSeries_DslopePhiCDifferentiableAt
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EisensteinSeries_DslopePhiCDifferentiableAt
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:25:27.059579+00:00
-- url     : https://prove2.me/theorems/0c71b372-1720-4d44-ad67-175178d74b07
-- title:
--   Dslope Phi CDifferentiable At
-- statement:
--   Definitions and structural lemmas for Dslope Phi CDifferentiable At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EisensteinSeries/DslopePhiCDifferentiableAt.lean

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
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.KroneckerLimitFormula
open Complex Asymptotics Filter Topology
def gC (y : ℝ) (s : ℂ) : ℂ :=
  2 * (y : ℂ) ^ (1 - s) * (Real.sqrt Real.pi : ℂ) * Gamma (s - 1 / 2) * (Gamma s)⁻¹
def PhiC (y : ℝ) (s : ℂ) : ℂ := gC y s * riemannZeta₁ (2 * s - 1) / 2
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.KroneckerLimitFormula
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5


