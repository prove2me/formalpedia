-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_IsLogSpaceUniform
-- name    : DoublyEffIP_Supplement_IsLogSpaceUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:29:55.732984+00:00
-- url     : https://prove2.me/theorems/7c8fbbd2-0d8b-419e-b270-af1c5d731ebf
-- title:
--   Log-space uniform family of implementation circuits
-- statement:
--   A transducer $T$ is a **log-space uniform** generator with constant $c$ if, for all $n$ and $B$, on input the shape $(1^n,1^B)$ it outputs the description of some circuit while using at most
--
--   $$
--   c\,\big(\lfloor\log_2(n+B+2)\rfloor+1\big)
--   $$
--
--   work cells.
--
--   This is the paper's notion "C is f-space uniform if there exists a fixed O(f(n))-space Turing machine M that, on input $1^n$, outputs the full description of the circuit $C_n$", with $f=\log$ and the shape parameters of an implementation circuit.
--
--   **Formalization Note** $O(\log)$ is $c(\log+1)$ with one constant for the whole family; space is the work tape of the transducer model (read-only input, write-only output).
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9, Definitions 3 and 5

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Circuit
import Definitions.Def_DoublyEffIP_Supplement_encCircuit
import Definitions.Def_DoublyEffIP_Supplement_implShape
import Definitions.Def_TreeEdgeRankPC_Transducer

set_option autoImplicit false

open TreeEdgeRankPC

namespace DoublyEffIP.Supplement

/-- **A log-space uniform family of implementation circuits** — Definitions 3 and 5 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…),
Section 3.2, p.9: "C is f-space uniform if there exists a fixed O(f(n))-space Turing machine M that,
on input 1^n, outputs the full description of the circuit C_n … An important special case is when
f(n) = log(n)", with the shape parameters `(1^n, 1^B)` of an implementation circuit
`C : F^{n+B} → F^m`.

`IsLogSpaceUniform T c`: for all `n` and `B`, on input `implShape n B` the transducer `T` outputs
the description of some circuit using at most `c · (⌊log₂(n + B + 2)⌋ + 1)` work cells.

**Formalization Note.** `O(log)` is `c · (log + 1)` with one constant `c` for the whole family; the
`+2` and `+1` avoid `log 0`. Space is the work tape of the published transducer model (read-only
input, write-only output). -/
def IsLogSpaceUniform (T : Transducer) (c : ℕ) : Prop :=
  ∀ n B : ℕ, ∃ C : Circuit,
    T.ComputesWithin (implShape n B) (encCircuit C) (c * (Nat.log 2 (n + B + 2) + 1))

end DoublyEffIP.Supplement


