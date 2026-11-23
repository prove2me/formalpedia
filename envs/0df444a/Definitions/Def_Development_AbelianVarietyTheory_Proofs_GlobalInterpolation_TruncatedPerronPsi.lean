-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:09.499796+00:00
-- url     : https://prove2.me/theorems/4d61a906-d5e1-4808-bda7-f8fd8a12e17c
-- title:
--   Truncated Perron Psi
-- statement:
--   Definitions and structural lemmas for Truncated Perron Psi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
namespace GlobalTheory.PerronPsi
noncomputable def w (N : ℕ) (B : ℝ) (n : ℕ) : ℝ :=
  (if n = N then 1 else 0) + (if n = N + 1 then 1 else 0)
    + B * (1 / ((N - n : ℕ) : ℝ) + 1 / ((n - (N + 1) : ℕ) : ℝ))
end GlobalTheory.PerronPsi


