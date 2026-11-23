-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
-- name    : ReciprocityTheory_SemistableReduction_SemiDegCE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:05.156829+00:00
-- url     : https://prove2.me/theorems/5155bfb3-7770-49b2-b1b7-319d4246fb7f
-- title:
--   Semi Deg CE
-- statement:
--   Definitions and structural lemmas for Semi Deg CE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCE.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
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
open scoped nonZeroDivisors Pointwise
def vecIdx {K : Type} [Field K] [NumberField K] {k : ℕ} (X : Submodule (𝓞 K) (Fin k → K)) : ℕ :=
  (intVec K k).toAddSubgroup.relIndex X.toAddSubgroup
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx


