-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtMellinSummatory
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtMellinSummatory
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:08.251149+00:00
-- url     : https://prove2.me/theorems/a429b71e-0a12-4f6d-9c33-bb9afd12836e
-- title:
--   Differentiable At Mellin Summatory
-- statement:
--   Definitions and structural lemmas for Differentiable At Mellin Summatory, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtMellinSummatory.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
namespace GlobalTheory.LGrowth
open Filter Topology Asymptotics
section General
variable {f : ℕ → ℂ} {C : ℝ}
noncomputable def summatory (f : ℕ → ℂ) (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k
end General
end GlobalTheory.LGrowth


