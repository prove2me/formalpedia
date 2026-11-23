-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:28.888214+00:00
-- url     : https://prove2.me/theorems/424f08a4-d986-44cf-b592-9bc2bf7932fd
-- title:
--   Norm Iterated FDeriv Rem Comp Le
-- statement:
--   Definitions and structural lemmas for Norm Iterated FDeriv Rem Comp Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
namespace GlobalTheory.CharFormDeriv
end GlobalTheory.CharFormDeriv
namespace GlobalTheory.CharFormDeriv
noncomputable def rem (t : ℝ) (y : ℝ) : ℂ :=
  (t : ℂ)⁻¹ * Complex.exp ((I * t) * y) + (-I) * y + (-(t : ℂ)⁻¹)
end GlobalTheory.CharFormDeriv
namespace GlobalTheory.CharFormDeriv
end GlobalTheory.CharFormDeriv
namespace GlobalTheory.CharFormDeriv
end GlobalTheory.CharFormDeriv
namespace GlobalTheory.CharFormDeriv
end GlobalTheory.CharFormDeriv


