-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
-- name    : ReciprocityTheory_SemistableReduction_SemiDegCA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:52.467335+00:00
-- url     : https://prove2.me/theorems/5601b3df-d355-47d5-b469-45c231eff9f6
-- title:
--   Semi Deg CA
-- statement:
--   Definitions and structural lemmas for Semi Deg CA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCA.lean

import Mathlib
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
open NumberField
open scoped nonZeroDivisors
def intVec (K : Type) [Field K] [NumberField K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx


