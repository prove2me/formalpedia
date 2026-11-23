-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
-- name    : ReciprocityTheory_SemistableReduction_SemiDegCD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:48.69771+00:00
-- url     : https://prove2.me/theorems/3705bb9c-b18e-4243-90b9-0598a91c1979
-- title:
--   Semi Deg CD
-- statement:
--   Definitions and structural lemmas for Semi Deg CD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCD.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
def rowMat {K : Type} [Field K] {k : ℕ} (z : Fin k → Fin k → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i a => z i a
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx


