-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:26.446836+00:00
-- url     : https://prove2.me/theorems/9b1be25c-febd-4514-a29b-467c86eac70d
-- title:
--   Psh Poisson
-- statement:
--   Definitions and structural lemmas for Psh Poisson, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric Real Filter Topology InnerProductSpace
namespace ReciprocityTheory.AnForm.A
noncomputable def poissonInt (g : ℂ → ℝ) (r : ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel 0 w • g) 0 r
end ReciprocityTheory.AnForm.A


