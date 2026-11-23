-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:55.344716+00:00
-- url     : https://prove2.me/theorems/06be63b9-b3b8-428f-b134-4e10555b73c3
-- title:
--   Psh Lap
-- statement:
--   Definitions and structural lemmas for Psh Lap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
namespace ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
end
end ReciprocityTheory.AnForm.A.PshLap
open MeasureTheory Metric Set Filter Topology Real
namespace ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
def Pr (G : ℂ → ℂ →L[ℝ] ℝ) (r : ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..2*π, G (circleMap 0 r θ) (circleMap 0 1 θ)
def Lap (H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (s : ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..2*π, (H (circleMap 0 s θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
    H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I))
end
end ReciprocityTheory.AnForm.A.PshLap
open MeasureTheory Metric Set Filter Topology Real
namespace ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
end
end ReciprocityTheory.AnForm.A.PshLap


