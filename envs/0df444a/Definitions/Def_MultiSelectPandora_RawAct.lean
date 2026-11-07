-- Prove2me | Definitions.Def_MultiSelectPandora_RawAct
-- name    : MultiSelectPandora_RawAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:03.944198+00:00
-- url     : https://prove2.me/theorems/ba6e7c95-30fd-441c-b7a5-9d3aaef168b4
-- title:
--   Outputs of a next-action machine
-- statement:
--   The output of a machine computing a policy: open the box of a given index, or stop and select the boxes of a list of indices.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Theorem 1.1, p.2 (PDF p.3); §2.1, p.5 (PDF p.6)

import Mathlib

namespace MultiSelectPandora

/-- **A machine's output**: open a box, or stop and select a list of boxes.
Auxiliary to §2.1, p.5 (PDF p.6) of the Beyhaghi–Han–Luqman manuscript. -/
inductive RawAct where
  /-- open the box of this index -/
  | openBox (i : ℕ)
  /-- stop and select the boxes of these indices -/
  | stop (S : List ℕ)

end MultiSelectPandora


