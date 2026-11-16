-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_IsSetSpaceUniform
-- name    : DoublyEffIP_Supplement_IsSetSpaceUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:30:50.425309+00:00
-- url     : https://prove2.me/theorems/79591b2a-f19e-4814-af7f-cc1d6fdf3eba
-- title:
--   $p$-space uniform family of set-description circuits
-- statement:
--   A transducer $T$ is a **$p$-space uniform** generator of set-description circuits with constant $c$ if, for all $m,B,p$, on input the shape $(m,1^B,1^p)$ it outputs the description of some circuit while using at most $c(p+1)$ work cells.
--
--   This is the uniformity of the implementation circuit $G:[k]\times\{0,1\}^B\to\{0,1\}^p$ of a description of a set (Definition 4).
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9, Definitions 3 and 4

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Circuit
import Definitions.Def_DoublyEffIP_Supplement_encCircuit
import Definitions.Def_DoublyEffIP_Supplement_setShape
import Definitions.Def_TreeEdgeRankPC_Transducer

set_option autoImplicit false

open TreeEdgeRankPC

namespace DoublyEffIP.Supplement

/-- **A `p`-space uniform family of set-description circuits** — Definitions 3 and 4 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…),
Section 3.2, p.9: "a (multi-output) p-space uniform circuit G : [k] × {0,1}^B → {0,1}^p", whose
generating machine takes the shape parameters `(k, 1^B, 1^p)`.

`IsSetSpaceUniform T c`: for all `m`, `B`, `p`, on input `setShape m B p` the transducer `T`
outputs the description of some circuit using at most `c · (p + 1)` work cells.

**Formalization Note.** `O(p)` is `c · (p + 1)` with one constant `c` for the whole family. -/
def IsSetSpaceUniform (T : Transducer) (c : ℕ) : Prop :=
  ∀ m B p : ℕ, ∃ C : Circuit, T.ComputesWithin (setShape m B p) (encCircuit C) (c * (p + 1))

end DoublyEffIP.Supplement


