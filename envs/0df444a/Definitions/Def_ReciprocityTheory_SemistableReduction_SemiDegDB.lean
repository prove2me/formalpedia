-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB
-- name    : ReciprocityTheory_SemistableReduction_SemiDegDB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:16.350808+00:00
-- url     : https://prove2.me/theorems/5b5ddedd-e7b6-482a-99eb-8b4b6c814d8d
-- title:
--   Semi Deg DB
-- statement:
--   Definitions and structural lemmas for Semi Deg DB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDB.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
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
open NumberField
def cutProjK (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[K] (Fin r → K) where
  toFun x i := if e ≤ (i : ℕ) then x i else 0
  map_add' x y := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]
variable {K : Type} [Field K] [NumberField K] {r e : ℕ}
end ReciprocityTheory.MultiplicativeHeights


