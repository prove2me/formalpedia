-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:25.216591+00:00
-- url     : https://prove2.me/theorems/99f456f9-c6e7-4c9b-accd-aa9b4dd9761c
-- title:
--   Schwartz Character Seminorm Bound
-- statement:
--   Definitions and structural lemmas for Schwartz Character Seminorm Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzCharacterSeminormBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
namespace GlobalTheory.PhaseLipschitz
def psi (k : ℝ) : ℝ → ℂ := fun t =>
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) - 1
end GlobalTheory.PhaseLipschitz


