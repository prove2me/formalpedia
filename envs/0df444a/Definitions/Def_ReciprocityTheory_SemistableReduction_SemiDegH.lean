-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH
-- name    : ReciprocityTheory_SemistableReduction_SemiDegH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:49.473261+00:00
-- url     : https://prove2.me/theorems/99920aff-8dff-45d9-938b-9b5e5d4e1e1c
-- title:
--   Semi Deg H
-- statement:
--   Definitions and structural lemmas for Semi Deg H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegH.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
def projLt (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if (i : ℕ) < e then x i else 0
  map_add' x y := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]
end ReciprocityTheory.MultiplicativeHeights.SemiPt


