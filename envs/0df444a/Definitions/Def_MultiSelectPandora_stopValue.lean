-- Prove2me | Definitions.Def_MultiSelectPandora_stopValue
-- name    : MultiSelectPandora_stopValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:29.961203+00:00
-- url     : https://prove2.me/theorems/81036959-58a1-466e-b892-da07fde933e3
-- title:
--   The expected value of a stop-and-select
-- statement:
--   When the searcher stops at history $h$ and selects $S$, the selection is worth
--   $$\sum_{i\in S}\begin{cases}\text{the value observed at } i, & i\text{ opened in }h,\\ E[v_i], & \text{otherwise.}\end{cases}$$
--   An opened box contributes its observed value, and a box claimed closed contributes its mean in expectation.
--
--   **Formalization Note** An out-of-range position never occurs on a reachable history; it falls back to the mean.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_mean
import Definitions.Def_MultiSelectPandora_History

namespace MultiSelectPandora

/-- **The expected value of a stop-and-select.** Beyhaghi–Han–Luqman manuscript, §2.1, p.5 (PDF p.6): an opened box
contributes its observed value; "a box claimed closed … contributes `E[v_i]` in expectation".

**Formalization Note.** `h.lookup i` is the position that came up if box `i` was opened. An out-of-range position
never occurs on a reachable history; it then falls back to the mean. -/
noncomputable def stopValue (I : Inst) (h : History I.n) (S : Finset (Fin I.n)) : ℝ :=
  ∑ i ∈ S, match h.lookup i with
    | some j => if hj : j < I.s i then I.val i ⟨j, hj⟩ else I.mean i
    | none => I.mean i

end MultiSelectPandora


