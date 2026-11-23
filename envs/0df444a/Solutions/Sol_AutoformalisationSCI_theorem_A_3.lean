-- Prove2me | solution 1 for AutoformalisationSCI.theorem_A_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T05:00:56.588817+00:00
-- url     : https://prove2.me/submissions/c2680df2-59be-413d-838c-2dd995e08b1d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AutoformalisationSCI_Arith
import Definitions.Def_AutoformalisationSCI_Oracle
import Definitions.Def_AutoformalisationSCI_Poly
import Theorems.Thm_AutoformalisationSCI_dSetL_two_eq_dSet
import Theorems.Thm_AutoformalisationSCI_theorem_A_4

set_option autoImplicit false

open AutoformalisationSCI

theorem solution (k : ℕ) (hk : 9 ≤ k) (E : ComputablePolyEnum (k + 1)) :
    SigmaComplete 2 (dSet k E) ∧ ¬ SetTuringReducible (dSet k E) (jumpIter 1) := by
  have heq := AutoformalisationSCI.dSetL_two_eq_dSet k E
  have hA4 := AutoformalisationSCI.theorem_A_4 2 k (by omega) hk
    (cast (congrArg ComputablePolyEnum (by omega : k + 1 = 2 - 1 + k)) E)
  simpa [heq] using hA4
