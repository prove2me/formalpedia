-- Prove2me | Definitions.Def_MultiSelectPandora_DPPolicy
-- name    : MultiSelectPandora_DPPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:20.715967+00:00
-- url     : https://prove2.me/theorems/0f009ff6-ddae-4090-af3c-ceeef99ec9d3
-- title:
--   Policies of the dynamic program
-- statement:
--   A policy of the dynamic program chooses each action as a function of the history of (action, position).
--
--   **Formalization Note** The position is that of the realized value on an opening and $0$ otherwise. A policy may read positions; the class reading only the values $w_i$ is defined separately. Policies are deterministic.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MultiSelectPandora_DPAct

namespace MultiSelectPandora

/-- **A policy of the dynamic program**: the next action as a function of the history of (action, position).
Beyhaghi–Han–Luqman manuscript, §3.1, p.7 (PDF p.8): "A policy chooses each action as a function of the history so far".

**Formalization Note.** The position is the support position that came up on an opening and `0` otherwise. A policy may read
positions; `IsSDiscretized` is the class that reads only the values `w_i`. Policies are deterministic. -/
abbrev DPPolicy (n : ℕ) : Type := List (DPAct n × ℕ) → DPAct n

end MultiSelectPandora


