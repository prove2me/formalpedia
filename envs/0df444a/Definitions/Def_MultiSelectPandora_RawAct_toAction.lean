-- Prove2me | Definitions.Def_MultiSelectPandora_RawAct_toAction
-- name    : MultiSelectPandora_RawAct_toAction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:12.863536+00:00
-- url     : https://prove2.me/theorems/3211f09b-7443-46bf-b686-ed65bc0267a5
-- title:
--   Reading a machine output as an action
-- statement:
--   A machine's output is read as an action on $n$ boxes. An index out of range, or a repeated index in a selection, is read as the malformed output, which is not admissible.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Theorem 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_MultiSelectPandora_Action
import Definitions.Def_MultiSelectPandora_RawAct

namespace MultiSelectPandora

/-- **Reading a machine's output as an action.** Auxiliary to §2.1, p.5 (PDF p.6) of the Beyhaghi–Han–Luqman manuscript.

**Formalization Note.** An out-of-range index, or a repeated one in a selection, reads as `Action.invalid`. -/
def RawAct.toAction (n : ℕ) : RawAct → Action n
  | .openBox i => if h : i < n then .openBox ⟨i, h⟩ else .invalid
  | .stop S =>
    if (∀ x ∈ S, x < n) ∧ S.Nodup then .stop (Finset.univ.filter fun i : Fin n => i.val ∈ S) else .invalid

end MultiSelectPandora


