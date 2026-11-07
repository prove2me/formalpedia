-- Prove2me | Definitions.Def_MultiSelectPandora_RawInst
-- name    : MultiSelectPandora_RawInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:00.404974+00:00
-- url     : https://prove2.me/theorems/d05131c8-ea51-4941-a1a5-aff9f4a429c2
-- title:
--   A rational instance as data
-- statement:
--   A rational instance is a list with one entry per box: the cost, and the list of (value, probability) pairs of its support. This is what "given explicitly, with finite support" means for an algorithm reading a finite word.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6); p.17 (PDF p.18)

import Mathlib

namespace MultiSelectPandora

/-- **A rational instance as data**: per box, the cost and the list of (value, probability).
Beyhaghi–Han–Luqman manuscript, §2.1, p.5 (PDF p.6): "Each `F_i` is given explicitly, with finite support".

**Formalization Note.** A Turing machine reads finite words, so machine statements take rational data; theorems that are
not about machines are stated over `ℝ`. -/
abbrev RawInst : Type := List (ℚ × List (ℚ × ℚ))

end MultiSelectPandora


