-- Prove2me | Definitions.Def_MultiSelectPandora_policyOf
-- name    : MultiSelectPandora_policyOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:06:46.997936+00:00
-- url     : https://prove2.me/theorems/21be88be-8aba-42f8-add0-5b5e37747dd8
-- title:
--   The policy computed by a next-action function
-- statement:
--   Given a function `next` from (rational instance, history) to outputs, the computed policy on an instance $I$ answers a history $h$ with the reading of `next`$(I,h)$.
--
--   This is how a policy is "computed": an explicit decision tree can have exponential size, so an algorithm describes it implicitly by producing the next action on demand. The block-adaptive trees of Fu, Li and Xu, used by the paper, are walked in this way.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Theorem 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_MultiSelectPandora_Policy
import Definitions.Def_MultiSelectPandora_RawInst
import Definitions.Def_MultiSelectPandora_RawInst_toInst
import Definitions.Def_MultiSelectPandora_RawAct
import Definitions.Def_MultiSelectPandora_RawAct_toAction

namespace MultiSelectPandora

/-- **The policy computed by a next-action function.** Beyhaghi–Han–Luqman manuscript, Theorem 1.1, p.2 (PDF p.3):
"computes a policy".

**Formalization Note.** An explicit decision tree can have exponential size, so a policy is computed implicitly: `next`
gets the instance and the history (with box indices as numbers) and returns the next action. -/
noncomputable def policyOf (next : RawInst × List (ℕ × ℕ) → RawAct) (I : RawInst) : Policy I.toInst.n :=
  fun h => (next (I, h.map fun e => (e.1.val, e.2))).toAction I.toInst.n

end MultiSelectPandora


