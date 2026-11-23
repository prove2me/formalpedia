-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotalDegreeLeOfIntegralAtInfinity
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotalDegreeLeOfIntegralAtInfinity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:04.041618+00:00
-- url     : https://prove2.me/theorems/88ece79d-68e5-4967-89ce-bec216694ffc
-- title:
--   Total Degree Le Of Integral At Infinity
-- statement:
--   Definitions and structural lemmas for Total Degree Le Of Integral At Infinity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TotalDegreeLeOfIntegralAtInfinity.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory.DegreeBound
variable {K : Type} [Field K] {D : ℕ}
def Good (y : Fin D → K) (j : Fin D) (N : ℕ) (b : K) : Prop :=
  ∃ C : MvPolynomial (Fin D) ℤ, C.totalDegree ≤ N ∧ b * y j ^ N = aeval y C
end GlobalTheory.DegreeBound


