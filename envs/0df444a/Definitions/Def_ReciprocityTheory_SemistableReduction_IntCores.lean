-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_IntCores
-- name    : ReciprocityTheory_SemistableReduction_IntCores
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:20.756892+00:00
-- url     : https://prove2.me/theorems/50f4819c-98d2-4354-9421-2df1cf303c62
-- title:
--   Int Cores
-- statement:
--   Definitions and structural lemmas for Int Cores, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCores.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
def blockSlice {B n : ℕ} (b : Fin B) (p : Fin B → Fin n → ℂ) :
    Fin B × Fin n → MvPolynomial (Fin n) ℂ :=
  fun q => if q.1 = b then X q.2 else C (p q.1 q.2)
end ReciprocityTheory.MultiplicativeHeights


