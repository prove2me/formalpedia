-- Prove2me | Definitions.Def_MultiSelectPandora_DPAct
-- name    : MultiSelectPandora_DPAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:35.384567+00:00
-- url     : https://prove2.me/theorems/1bb65a2a-bb1a-4622-b0c1-658492e3a810
-- title:
--   Actions of the dynamic program
-- statement:
--   For each box $i$, the action $a_i^0$ (open) and the action $a_i^1$ (claim closed), and the action *end*, which leaves the state unchanged.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Table 1, p.7 (PDF p.8)

import Mathlib

namespace MultiSelectPandora

/-- **The actions of the dynamic program.** Beyhaghi–Han–Luqman manuscript, Table 1, p.7 (PDF p.8): `a⁰_i` (open), `a¹_i`
(claim closed), and `end`. -/
inductive DPAct (n : ℕ) where
  /-- `a⁰_i`, open box `i` -/
  | openBox (i : Fin n)
  /-- `a¹_i`, claim box `i` closed -/
  | claim (i : Fin n)
  /-- `end`, which leaves the state unchanged -/
  | stop
  deriving DecidableEq

end MultiSelectPandora


