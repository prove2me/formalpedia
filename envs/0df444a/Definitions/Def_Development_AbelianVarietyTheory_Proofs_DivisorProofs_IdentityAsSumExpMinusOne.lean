-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:11.826749+00:00
-- url     : https://prove2.me/theorems/ce883005-494f-4486-a0dd-10c024239e62
-- title:
--   Identity As Sum Exp Minus One
-- statement:
--   Definitions and structural lemmas for Identity As Sum Exp Minus One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
namespace GlobalTheory.ExpDivision
noncomputable def quot (a : ℝ) : ℂ → ℂ := dslope (fun z => Complex.exp (Complex.I * (a * z))) 0
end GlobalTheory.ExpDivision


