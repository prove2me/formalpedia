-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAB
-- name    : ReciprocityTheory_SemistableReduction_SemiDegAB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:21.394061+00:00
-- url     : https://prove2.me/theorems/d1131dfa-21dd-4b1f-8c1f-b4add64ab5f2
-- title:
--   Semi Deg AB
-- statement:
--   Definitions and structural lemmas for Semi Deg AB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAB.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
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
open Module
def waExt {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) : Fin (n + 2) → α :=
  Fin.cons x (Fin.snoc f y : Fin (n + 1) → α)
end ReciprocityTheory.MultiplicativeHeights


