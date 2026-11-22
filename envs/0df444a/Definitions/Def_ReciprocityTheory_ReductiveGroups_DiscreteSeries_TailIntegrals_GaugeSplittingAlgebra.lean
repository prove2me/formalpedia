-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:14:46.036725+00:00
-- url     : https://prove2.me/theorems/d4cc9efc-993d-40df-9686-476cca007ee9
-- title:
--   Gauge Splitting Algebra
-- statement:
--   Definitions and structural lemmas for Gauge Splitting Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaugeSplittingAlgebra.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace J2
def sclPt {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) :
    (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ :=
  (Fin.cons a0 (r • x.1), r • x.2.1, r • x.2.2.1, r ^ 2 * x.2.2.2)
end J2
end ReciprocityTheory.ChartRestriction.DS.Xi


