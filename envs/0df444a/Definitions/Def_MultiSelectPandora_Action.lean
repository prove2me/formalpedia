-- Prove2me | Definitions.Def_MultiSelectPandora_Action
-- name    : MultiSelectPandora_Action
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:33.047599+00:00
-- url     : https://prove2.me/theorems/688cb6ae-5595-4da7-8ccf-66b870c39d88
-- title:
--   Actions of the searcher
-- statement:
--   At each point the searcher either opens a box $i$, or stops and selects a set $S$ of boxes. A selected box that has not been opened is claimed closed. Since $\hat k=k$ for k-PNOI, the budget on closed claims follows from $|S|\le k$.
--
--   **Formalization Note** A third constructor `invalid` is the reading of a malformed machine output, such as an out-of-range index. It is not an action of the model: it is never admissible and it scores $0$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib

namespace MultiSelectPandora

/-- **An action of the searcher.** Beyhaghi–Han–Luqman manuscript, §2.1, p.5 (PDF p.6): "open a box or … stop and select".

**Formalization Note.** `invalid` is not an action of the page. It is the reading of a malformed machine output (an
out-of-range index, see `RawAct.toAction`); it is never admissible and scores `0`. A selected box that is not opened is
claimed closed. Since `k̂ = k`, the budget `Σ A_i (1 − I_i) ≤ k̂` follows from `Σ A_i ≤ k`. -/
inductive Action (n : ℕ) where
  /-- open box `i` -/
  | openBox (i : Fin n)
  /-- stop and select the boxes of `S` -/
  | stop (S : Finset (Fin n))
  /-- a malformed output -/
  | invalid

end MultiSelectPandora


