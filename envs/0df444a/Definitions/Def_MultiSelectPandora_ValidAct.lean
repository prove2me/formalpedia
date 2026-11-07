-- Prove2me | Definitions.Def_MultiSelectPandora_ValidAct
-- name    : MultiSelectPandora_ValidAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:08.203779+00:00
-- url     : https://prove2.me/theorems/3b2e5243-3afd-4897-9ddf-71db040f06f9
-- title:
--   Valid actions
-- statement:
--   Given a history $h$, opening box $i$ is valid when $i$ has not been opened in $h$, and stopping with $S$ is valid when $|S|\le k$, that is $\sum_iA_i\le k$. The malformed output is never valid.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_History
import Definitions.Def_MultiSelectPandora_Action

namespace MultiSelectPandora

/-- **When an action is valid.** Beyhaghi–Han–Luqman manuscript, §2.1, p.5 (PDF p.6): only an unopened box is opened,
and at most `k` boxes are selected (`Σ_i A_i ≤ k`). -/
def ValidAct (I : Inst) (k : ℕ) (h : History I.n) : Action I.n → Prop
  | .openBox i => h.lookup i = none
  | .stop S => S.card ≤ k
  | .invalid => False

end MultiSelectPandora


