-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:25.382554+00:00
-- url     : https://prove2.me/theorems/9615dff4-145f-4d4d-b294-21bbdfae45d3
-- title:
--   Gelfand Series
-- statement:
--   Definitions and structural lemmas for Gelfand Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean

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
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def gx (l : Fin n → ℂ) : ℕ → Fin n → ℂ
  | 0, _ => 1
  | k + 1, r => l r * gx l k r - ∑ s ∈ univ.filter (fun s => r < s), gx l k s
def gelfandSeries (l : Fin n → ℂ) : PowerSeries ℂ :=
  1 - ∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹)
def gval (l : Fin n → ℂ) (k : ℕ) : ℂ := PowerSeries.coeff (k + 1) (gelfandSeries l)
def icShift (μ : Fin n → ℝ) : Fin n → ℂ := fun r => ((μ r + ((n : ℝ) - 1) / 2 : ℝ) : ℂ)
def gxSeries (l : Fin n → ℂ) (r : Fin n) : PowerSeries ℂ := PowerSeries.mk fun k => gx l k r
end ReciprocityTheory.ChartRestriction.DS


