-- Prove2me | Definitions.Def_QStateSearch_bitsBefore
-- name    : QStateSearch_bitsBefore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:31.604366+00:00
-- url     : https://prove2.me/theorems/448f8eed-0579-48dd-ac11-9e001d11f4cf
-- title:
--   Prover bits before a query slot, $B_t$
-- statement:
--   For a step list and a query slot $t$ (counted from $0$), $B_t$ is the sum of the padded lengths $b$ of the prover messages that come before that slot.
--
--   **Formalization Note** Slot $t$ in Lean is the paper's query $t+1$ (the paper counts $t\in[q]$ from $1$). For $t$ beyond the last query the value is the total number of prover bits.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.2, p.10

import Mathlib
import Definitions.Def_QStateSearch_Step

namespace QStateSearch

/-- `bitsBefore steps t`: the sum of the padded lengths of the prover messages that come before
the query slot with 0-based index `t`, the paper's `B_t`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.2, p.10: "For slot t, let B_t be the sum of the padded lengths of the prover
messages in earlier communication slots."

**Formalization Note.** Slots are 0-based in Lean: Lean slot `t` is the paper's slot `t + 1`
(the paper's `t ∈ [q]` is 1-based). For `t` at least the number of query steps the value is
the total of all prover bits. -/
def bitsBefore {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] : List (Step D W) → ℕ → ℕ
  | [], _ => 0
  | .query :: _, 0 => 0
  | .query :: rest, t + 1 => bitsBefore rest t
  | .unitary _ :: rest, t => bitsBefore rest t
  | .vmsg _ _ :: rest, t => bitsBefore rest t
  | .pmsg b _ :: rest, t => b + bitsBefore rest t

end QStateSearch


