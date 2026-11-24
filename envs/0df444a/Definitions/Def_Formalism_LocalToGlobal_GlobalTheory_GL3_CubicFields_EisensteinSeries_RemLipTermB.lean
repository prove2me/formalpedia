-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EisensteinSeries_RemLipTermB
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EisensteinSeries_RemLipTermB
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:37:44.494926+00:00
-- url     : https://prove2.me/theorems/9ffd5772-eaf6-431b-b9f2-e29cc64e3c8f
-- title:
--   Rem Lip Term B
-- statement:
--   Definitions and structural lemmas for Rem Lip Term B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EisensteinSeries/RemLipTermB.lean

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EisensteinSeries_RemLipTermA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT
open MeasureTheory
def maj (y b t : ℝ) (a : ℝ) (s : ℝ) : ℝ := (s - 1) * (2 * Real.exp |Real.log y| * y) *
  ((1 + 2 * |Real.log y| + 4 * |Real.log b|) * qv a b t ^ (-(3 / 2) : ℝ) + 4 / b * qv a b t ^ (-1 : ℝ))
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT


