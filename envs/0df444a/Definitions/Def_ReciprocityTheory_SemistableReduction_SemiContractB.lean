-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractB
-- name    : ReciprocityTheory_SemistableReduction_SemiContractB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:29.832588+00:00
-- url     : https://prove2.me/theorems/9e6fdaa7-0c76-4d3f-baae-b8187fac6efe
-- title:
--   Semi Contract B
-- statement:
--   Definitions and structural lemmas for Semi Contract B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractB.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder
def embCols {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} (σ : K →+* ℂ)
    (v : ι → Fin r → K) : Matrix (Fin r) ι ℂ :=
  Matrix.of fun a i => σ (v i a)
end ReciprocityTheory.MultiplicativeHeights


