-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EisensteinSeries_RemLipTermA
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EisensteinSeries_RemLipTermA
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:25:43.876937+00:00
-- url     : https://prove2.me/theorems/d6d342ab-13d8-4483-aec4-86042986b0ab
-- title:
--   Rem Lip Term A
-- statement:
--   Definitions and structural lemmas for Rem Lip Term A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EisensteinSeries/RemLipTermA.lean

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
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT
open MeasureTheory
def qv (a b t : ℝ) : ℝ := (t + a) ^ 2 + b ^ 2
def fF (y a b σ t : ℝ) : ℝ := y ^ σ * qv a b t ^ (-σ)
def fF' (y a b σ t : ℝ) : ℝ := -2 * σ * y ^ σ * (t + a) * qv a b t ^ (-σ - 1)
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT


