-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:43.946889+00:00
-- url     : https://prove2.me/theorems/4c104a38-a681-4b05-88df-66db69aaae8d
-- title:
--   Schwartz Seminorm Smul Left Linear Phase Le
-- statement:
--   Definitions and structural lemmas for Schwartz Seminorm Smul Left Linear Phase Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormSmulLeftLinearPhaseLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open Complex
namespace GlobalTheory.LinPhaseSeminorm
noncomputable def phaseLine (c t : ℝ) : ℝ → ℂ := fun y =>
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t ^ 2 * c : ℝ) : ℂ)) *
    Complex.exp ((-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ))
end GlobalTheory.LinPhaseSeminorm


