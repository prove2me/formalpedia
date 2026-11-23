-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCB
-- name    : ReciprocityTheory_SemistableReduction_SemiDegCB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:22.503907+00:00
-- url     : https://prove2.me/theorems/4209a8e0-1297-4218-94e7-2b78a5346869
-- title:
--   Semi Deg CB
-- statement:
--   Definitions and structural lemmas for Semi Deg CB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCB.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
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
def consZero (K : Type) [Field K] (k : ℕ) : (Fin k → K) →ₗ[K] (Fin (k + 1) → K) where
  toFun y := Fin.cons 0 y
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx


