-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_ClassNumberQuad
-- name    : Formalism_UnipotentAdelicQuotients_ClassNumberQuad
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:27.299802+00:00
-- url     : https://prove2.me/theorems/bcb52179-43bc-4925-a224-b90d03d0a2e3
-- title:
--   Class Number Quad
-- statement:
--   Definitions and structural lemmas for Class Number Quad, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/ClassNumberQuad.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open NumberField Module
namespace HeckeCharacterZeroLocus.ClassNumberQuad
def ClassNumberLe : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], finrank ℚ K = 2 → IsTotallyComplex K →
    (classNumber K : ℝ) ≤ Real.sqrt (|discr K| : ℝ) * (Real.log (|discr K| : ℝ) + 2) / Real.pi
end HeckeCharacterZeroLocus.ClassNumberQuad


