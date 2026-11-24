-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:19.538799+00:00
-- url     : https://prove2.me/theorems/4b738eae-bf33-4d6a-9bc5-f62360236d76
-- title:
--   Psh Ext A
-- statement:
--   Definitions and structural lemmas for Psh Ext A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtA.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
section
noncomputable def pert (E : Finset ℂ) (c : ℂ) (ε δ : ℝ) (ζ : ℂ) : ℝ :=
  ε * ∑ f ∈ E, log ‖ζ - f‖ + δ * ‖ζ - c‖ ^ 2
end
section
end
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension


