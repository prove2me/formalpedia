-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:39.642569+00:00
-- url     : https://prove2.me/theorems/e40756e3-41d3-4cba-be22-38e86b7bb8c4
-- title:
--   Four Sum
-- statement:
--   Definitions and structural lemmas for Four Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourSum.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
def fsProj (f : ℕ) : (Fin f → ℝ) → UnitAddTorus (Fin f) := fun t i => (t i : UnitAddCircle)
theorem fsProj_isOpenQuotientMap (f : ℕ) : IsOpenQuotientMap (fsProj f) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
def fsFun {f : ℕ} (g : (Fin f → ℝ) → ℂ) : UnitAddTorus (Fin f) → ℂ :=
  fun θ => g (Function.surjInv (fsProj_isOpenQuotientMap f).surjective θ)
end
end ReciprocityTheory.L2DbarEstimates.Y


