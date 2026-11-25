-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantSurjective
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_JInvariantSurjective
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:57:31.239276+00:00
-- url     : https://prove2.me/theorems/50ddf918-1a1b-5af3-b129-66a38f2e1150
-- title:
--   JInvariant Surjective
-- statement:
--   Definitions and structural lemmas for JInvariant Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/JInvariantSurjective.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology Set
open scoped PeriodPair Real Modular
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
def modularJC (z : ℂ) : ℂ := modularJ (ofComplex z)
def fdBelow (A : ℝ) : Set ℂ :=
  {z | 1 ≤ normSq z ∧ |z.re| ≤ 1 / 2 ∧ 0 ≤ z.im ∧ z.im ≤ A}
end Elliptic
end GroundTheory.Global


