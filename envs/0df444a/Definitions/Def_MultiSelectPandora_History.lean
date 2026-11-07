-- Prove2me | Definitions.Def_MultiSelectPandora_History
-- name    : MultiSelectPandora_History
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:49.151191+00:00
-- url     : https://prove2.me/theorems/cd43d5d5-8ff2-4a8d-854a-cf8be6b50379
-- title:
--   Histories
-- statement:
--   A history is the list, in opening order, of the boxes opened so far together with the support position that came up for each. It records "the boxes opened and the values observed so far": a position determines its value.
--
--   **Formalization Note** Histories record positions rather than values. Branching on which of two equal-valued positions came up is a mixture of deterministic choices and gains nothing. One policy type therefore serves real and rational instances, and a machine can read a history without seeing real numbers.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib

namespace MultiSelectPandora

/-- **A history**: which boxes were opened and which support position came up, in opening order.
Beyhaghi–Han–Luqman manuscript, §2.1, p.5 (PDF p.6): "the boxes opened and the values observed so far".

**Formalization Note.** A history records support *positions*, not values; values are read off the instance. Branching
on which of two equal-valued positions came up is a mixture and gains nothing. This lets one policy type serve real and
rational instances, and lets a machine read a history without seeing real numbers. -/
abbrev History (n : ℕ) : Type := List (Fin n × ℕ)

end MultiSelectPandora


