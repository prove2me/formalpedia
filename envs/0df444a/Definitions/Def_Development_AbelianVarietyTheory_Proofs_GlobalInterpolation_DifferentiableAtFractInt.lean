-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:01.531799+00:00
-- url     : https://prove2.me/theorems/db6748f0-f631-465d-be12-f031401ecfa0
-- title:
--   Differentiable At Fract Int
-- statement:
--   Definitions and structural lemmas for Differentiable At Fract Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology
namespace GlobalTheory.ZetaHalfPlane
noncomputable def fractInt (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
noncomputable def cutFract : ℝ → ℂ := (Ioi (1 : ℝ)).indicator fun t => ((Int.fract t : ℝ) : ℂ)
end GlobalTheory.ZetaHalfPlane


