-- Prove2me | Definitions.Def_MultiSelectPandora_Policy
-- name    : MultiSelectPandora_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:03.040935+00:00
-- url     : https://prove2.me/theorems/23c0cc21-2200-491e-8ec0-bde549fe5f19
-- title:
--   Policies
-- statement:
--   A policy $\pi$ maps each history to the next action.
--
--   **Formalization Note** Policies are deterministic. A randomized policy is a mixture of deterministic policies over finite supports, so it cannot beat the best deterministic one; the paper's decision trees on p.8 are deterministic too.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6); p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_History
import Definitions.Def_MultiSelectPandora_Action

namespace MultiSelectPandora

/-- **A policy**: the next action as a function of the history. Beyhaghi–Han–Luqman manuscript, §2.1, p.5 (PDF p.6).

**Formalization Note.** Policies are deterministic. A randomized policy is a mixture of deterministic ones over finite
supports, so it cannot beat the best deterministic one; p.8 (PDF p.9) itself works with deterministic decision trees. -/
abbrev Policy (n : ℕ) : Type := History n → Action n

end MultiSelectPandora


