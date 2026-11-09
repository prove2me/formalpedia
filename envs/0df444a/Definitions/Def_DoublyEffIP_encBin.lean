-- Prove2me | Definitions.Def_DoublyEffIP_encBin
-- name    : DoublyEffIP_encBin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:02.468138+00:00
-- url     : https://prove2.me/theorems/5c92c1a0-c3e7-46f1-8249-00c2a90f0067
-- title:
--   Self-delimited binary numeral $\langle m\rangle$
-- statement:
--   For a natural number $m$, the word $\langle m\rangle\in\{0,1\}^*$ is the binary expansion of $m$ (least significant bit first, with $0$ written as the single bit $0$), in which every bit $b$ is written as the pair $1\,b$ and the end is marked by a final $0$.
--
--   A word that begins with $\langle m\rangle$ determines $m$ and the rest of the word, so numbers can be concatenated with other data without separators. This is the encoding of the public parameters and of the round index given to the machines of a protocol.
--
--   **Formalization Note** The binary word and the framing are the published `countWord` and `frame` of the `SubexponentialSAT` definition.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, p.10 (encoding of the public parameters)

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace DoublyEffIP

/-- **A natural number in binary, self-delimited** — the encoding of the public parameters and of
the round index in Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*,
arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, p.10.

`encBin m` is the binary word of `m`, least significant bit first (`countWord`, with `0 ↦ [false]`),
wrapped by `frame`, which writes each bit `b` as `true, b` and ends with `false`. A word that starts
with `encBin m` therefore determines `m` and the rest of the word.

**Formalization Note.** The paper says only that both parties "have explicit access to the input
parameters pp"; binary is the standard reading. Encoders are those of the published
`SubexponentialSAT` definition. -/
def encBin (m : ℕ) : List Bool := Encoding.frame (SqrtLogSpace.countWord m)

end DoublyEffIP


