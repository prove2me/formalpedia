-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:15.397674+00:00
-- url     : https://prove2.me/theorems/19b734cd-3999-4e2b-84ec-cceef079a714
-- title:
--   Four Indep
-- statement:
--   Definitions and structural lemmas for Four Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourIndep.lean

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
open MeasureTheory Filter Topology Set
open scoped Interval
noncomputable section
def fiBox (m : ℕ) : Set (Fin m → ℝ) := Set.univ.pi (fun _ : Fin m => Set.Ioc (0 : ℝ) 1)
def fiG {f : ℕ} (h : (Fin f → ℂ) → ℂ) (ν : Fin f → ℤ) (s : Fin f → ℂ) : ℂ :=
  h s * Complex.exp (-2 * Real.pi * Complex.I * ∑ k, (ν k : ℂ) * s k)
end
end ReciprocityTheory.L2DbarEstimates.Y


