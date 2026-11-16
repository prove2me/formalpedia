-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_IsImpl
-- name    : DoublyEffIP_Supplement_IsImpl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:29:16.351203+00:00
-- url     : https://prove2.me/theorems/8901822f-52b9-4233-a8f0-c8f728a8845c
-- title:
--   The circuit output by a generating machine
-- statement:
--   A deterministic transducer $T$ **generates** the circuit $C$ on the shape word $w$ if, started on input $w$, it halts with the description $\langle C\rangle$ on its output.
--
--   The transducer is deterministic and descriptions are self-delimiting, so the generated circuit is unique. This is how a description $\langle\Phi\rangle$ is tied to its implementation circuit.
--
--   **Formalization Note** Machines are the published `TreeEdgeRankPC.Transducer`: a read-only input tape, one work tape, and a write-only output.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9, Definition 3

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Circuit
import Definitions.Def_DoublyEffIP_Supplement_encCircuit
import Definitions.Def_TreeEdgeRankPC_Transducer

set_option autoImplicit false

open TreeEdgeRankPC

namespace DoublyEffIP.Supplement

/-- **The circuit a generating machine outputs** — Definition 3 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9: a
machine "that, on input 1^n, outputs the full description of the circuit C_n".

`IsImpl T shape C`: on the input word `shape`, the transducer `T` halts with the description
`encCircuit C` of `C` on its output tape (with some finite workspace).

**Formalization Note.** The machine is the published `TreeEdgeRankPC.Transducer`: a deterministic
transducer with a read-only input tape, one work tape and a write-only output. It is deterministic
and `encCircuit` is self-delimiting, so `C` is unique. -/
def IsImpl (T : Transducer) (shape : List Bool) (C : Circuit) : Prop :=
  ∃ s : ℕ, T.ComputesWithin shape (encCircuit C) s

end DoublyEffIP.Supplement


