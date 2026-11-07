-- Prove2me | Definitions.Def_MultiSelectPandora_SSDPPolicy
-- name    : MultiSelectPandora_SSDPPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:37.189784+00:00
-- url     : https://prove2.me/theorems/22d91094-b690-4295-9f73-806327ecdc85
-- title:
--   Policies of a table
-- statement:
--   A policy of a table chooses each action index as a function of the history of (action index, outcome index).
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8)

import Mathlib

namespace MultiSelectPandora

/-- **A policy of a table**: the next action index as a function of the history of (action index, outcome index). Beyhaghi–Han–Luqman
manuscript, §3.1, p.7 (PDF p.8): "A policy chooses each action as a function of the history so far". -/
abbrev SSDPPolicy : Type := List (ℕ × ℕ) → ℕ

end MultiSelectPandora


