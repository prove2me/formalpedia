-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_AltSum
-- name    : GroundTheory_AutomorphicForms_CuspidalDiscreteness_AltSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:16.596179+00:00
-- url     : https://prove2.me/theorems/252a92fb-4677-47b9-8889-87b8e38c0763
-- title:
--   Alt Sum
-- statement:
--   Definitions and structural lemmas for Alt Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/AltSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace GroundTheory.Automorphic
def altSum {V W : Type*} [AddCommGroup V] [AddCommGroup W] :
    (k : ℕ) → (V → W) → (Fin k → V) → V → W
  | 0, h, _, s => h s
  | k + 1, h, y, s => altSum k (fun t => h (t + y 0) - h t) (Fin.tail y) s
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
def altSign {k : ℕ} (ε : Fin k → Bool) : ℤ := ∏ i, if ε i then 1 else -1
def altPoint {k : ℕ} (y : Fin k → V) (ε : Fin k → Bool) : V := ∑ i, if ε i then y i else 0
end GroundTheory.Automorphic


