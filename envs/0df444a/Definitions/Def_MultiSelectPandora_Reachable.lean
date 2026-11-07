-- Prove2me | Definitions.Def_MultiSelectPandora_Reachable
-- name    : MultiSelectPandora_Reachable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:43.660208+00:00
-- url     : https://prove2.me/theorems/7e624a9d-6697-405b-9e1e-16d0b5dd0f3f
-- title:
--   Histories reachable under a policy
-- statement:
--   The histories reachable under $\pi$ are the smallest set containing the empty history and closed under the following step: if $h$ is reachable, $\pi(h)$ opens a box $i$ not yet opened, and position $j$ has positive probability, then $h$ followed by $(i,j)$ is reachable. Each box occurs at most once in a reachable history.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_History
import Definitions.Def_MultiSelectPandora_Action
import Definitions.Def_MultiSelectPandora_Policy

namespace MultiSelectPandora

/-- **Histories reachable under a policy.** Auxiliary to §2.1, p.5 (PDF p.6) of the Beyhaghi–Han–Luqman manuscript.

**Formalization Note.** Only positions of positive probability are followed; a validly reachable history holds each box
at most once, so its length is at most `n`. -/
inductive Reachable (I : Inst) (π : Policy I.n) : History I.n → Prop
  /-- the empty history -/
  | nil : Reachable I π []
  /-- opening an unopened box and seeing a position of positive probability -/
  | step {h : History I.n} {i : Fin I.n} (j : Fin (I.s i)) : Reachable I π h → π h = .openBox i →
      h.lookup i = none → 0 < I.prob i j → Reachable I π (h ++ [(i, j.val)])

end MultiSelectPandora


