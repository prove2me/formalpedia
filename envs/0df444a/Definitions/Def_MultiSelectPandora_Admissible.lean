-- Prove2me | Definitions.Def_MultiSelectPandora_Admissible
-- name    : MultiSelectPandora_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:07:30.574573+00:00
-- url     : https://prove2.me/theorems/38240cc8-4df0-4ab3-ac21-9b75c8bdec96
-- title:
--   Admissible policies
-- statement:
--   A policy is admissible when its action is valid at every reachable history: it only opens unopened boxes and selects at most $k$ boxes. These are the policies of the model.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Policy
import Definitions.Def_MultiSelectPandora_ValidAct
import Definitions.Def_MultiSelectPandora_Reachable

namespace MultiSelectPandora

/-- **Admissible policies.** Beyhaghi–Han–Luqman manuscript, §2.1, p.5 (PDF p.6): a policy of the model opens unopened
boxes and selects at most `k` boxes.

**Formalization Note.** Validity is required at every reachable history (positions of positive probability). -/
def Admissible (I : Inst) (k : ℕ) (π : Policy I.n) : Prop :=
  ∀ h, Reachable I π h → ValidAct I k h (π h)

end MultiSelectPandora


