-- Prove2me | Definitions.Def_TetraOT_Supplement_redBlackBobTable
-- name    : TetraOT_Supplement_redBlackBobTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:38:12.610107+00:00
-- url     : https://prove2.me/theorems/2b69d749-cb00-4983-86f8-7569e1d451e1
-- title:
--   Bob's red-black table (Fig. 24)
-- statement:
--   With the labels $0,1,2,3 = L0,L1,R0,R1$ of Fig. 20, Bob reads his oblivious-transfer output $(s, m_s)$ directly off his card: $s$ is the side of the card ($L=0$, $R=1$) and $m_s$ its bit value.
--
--   | card | $s$ | $m_s$ | pattern |
--   |---|---|---|---|
--   | L0 | 0 | 0 | $0\bullet$ |
--   | L1 | 0 | 1 | $1\bullet$ |
--   | R0 | 1 | 0 | $\bullet 0$ |
--   | R1 | 1 | 1 | $\bullet 1$ |
--
--   **Formalization Note** Bits are Booleans with $\texttt{true}=1$, and the output is the pair $(s, m_s)$, the same encoding as the published Tetrahedral table $B$.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Figs. 20 and 24, pp.10–11 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib

set_option autoImplicit false

namespace TetraOT.Supplement

/-- **Bob's red-black table** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Fig. 24, p.11, with the card labels of Fig. 20,
p.10; p. = PDF page, the PDF has no printed page numbers). Fig. 24:

| card | s | m_s | m₀m₁ |
|------|---|-----|------|
| L0   | 0 | 0   | 0•   |
| L1   | 0 | 1   | 1•   |
| R0   | 1 | 0   | •0   |
| R1   | 1 | 1   | •1   |

`redBlackBobTable c = (s, m_s)` for Bob's card `c` (`0 = L0, 1 = L1, 2 = R0, 3 = R1`): "Bob takes the
'left-right zero-one' label of his card at face value" (p.10).

**Formalization Note.** Bits are `Bool` with `true` = 1; the output is Bob's ROT output `(s, m_s)`, the
same encoding as the published `TetraOT.bobTable` ("b•" ↦ `(false, b)`, "•b" ↦ `(true, b)`). -/
def redBlackBobTable : Fin 4 → Bool × Bool :=
  ![(false, false), (false, true), (true, false), (true, true)]

end TetraOT.Supplement


