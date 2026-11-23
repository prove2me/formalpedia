-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:48.056091+00:00
-- url     : https://prove2.me/theorems/0d10068f-fb2a-4479-ae88-c96df13d24c0
-- title:
--   Right Invariant GLOf Upper Triangular Right Invariant
-- statement:
--   Definitions and structural lemmas for Right Invariant GLOf Upper Triangular Right Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariant.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
namespace GlobalTheory
section Lower
variable {k : Type} [Field k] {m : ℕ}
def swapLine (i j : Fin m) (t : k) : Matrix (Fin m) (Fin m) k :=
  (1 - single j j 1 - single i i 1 + single j i 1 + single i j 1) + t • single j j 1
def upperFactor (i j : Fin m) (x : k) : Matrix (Fin m) (Fin m) k :=
  diagonal (Function.update (Function.update (1 : Fin m → k) j x⁻¹) i (-x)) * transvection j i x
end Lower
section Main
variable {k : Type} [Field k] [Infinite k] {m : ℕ}
end Main
end GlobalTheory


