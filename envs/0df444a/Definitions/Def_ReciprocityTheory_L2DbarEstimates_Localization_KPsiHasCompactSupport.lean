-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_KPsiHasCompactSupport
-- name    : ReciprocityTheory_L2DbarEstimates_Localization_KPsiHasCompactSupport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:27.157498+00:00
-- url     : https://prove2.me/theorems/bceead85-9ef6-4155-85f7-9e1904a818f5
-- title:
--   KPsi Has Compact Support
-- statement:
--   Definitions and structural lemmas for KPsi Has Compact Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/KPsiHasCompactSupport.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
def kPsi {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (φ : M → ℂ)
    (j k : Fin n) : M → V n :=
  fun x => ((Real.exp (ph x) : ℝ) : ℂ) •
    ((starRingEnd ℂ) (db n z j φ x) • bas n k - (starRingEnd ℂ) (db n z k φ x) • bas n j)
end
end ReciprocityTheory.L2DbarEstimates.F


