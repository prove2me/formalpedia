-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:23.783459+00:00
-- url     : https://prove2.me/theorems/e5fd677f-1cc0-45bf-be79-fd4f7f59cd60
-- title:
--   Psh Mean
-- statement:
--   Definitions and structural lemmas for Psh Mean, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
namespace ReciprocityTheory.AnForm.A.PshMean
noncomputable section
variable {D : ℕ}
end
end ReciprocityTheory.AnForm.A.PshMean
open MeasureTheory Metric Set Filter Topology Real
open scoped ContDiff
namespace ReciprocityTheory.AnForm.A.PshMol
noncomputable section
def b0 : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
def g0 (D : ℕ) (w : Fin D → ℂ) : ℝ := b0 (∑ i, ‖w i‖ ^ 2)
end
end ReciprocityTheory.AnForm.A.PshMol


