-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentOfDetMemNonZeroDivisors
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentOfDetMemNonZeroDivisors
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:39.484745+00:00
-- url     : https://prove2.me/theorems/0c5e2fb8-7ccb-45bb-bd1a-c4dff51e182f
-- title:
--   Linear Independent Of Det Mem Non Zero Divisors
-- statement:
--   Definitions and structural lemmas for Linear Independent Of Det Mem Non Zero Divisors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentOfDetMemNonZeroDivisors.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule Function
namespace GlobalTheory
namespace MaximalMinor
section Cramer
variable {A R F ι κ : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup F]
  [Module R F] [Module A F] [IsScalarTower A R F] [Fintype ι] [DecidableEq ι]
end Cramer
end MaximalMinor
end GlobalTheory


