-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:38.212281+00:00
-- url     : https://prove2.me/theorems/0ff52948-0b7a-4650-9fbd-9b846847f316
-- title:
--   Integral Ioi Fs Dens Radial
-- statement:
--   Definitions and structural lemmas for Integral Ioi Fs Dens Radial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section
def fsDens (z : ℂ) : ℝ := 1 / (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)
end
end ReciprocityTheory.AnForm


