-- Prove2me | Definitions.Def_TetraOT_bobTable
-- name    : TetraOT_bobTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:42.848522+00:00
-- url     : https://prove2.me/theorems/e85a407a-2d18-4851-88c7-c10aa08442c2
-- title:
--   Bob's lookup table $B(M,\rho(2)) = (y_0, y_1)$ (Fig. 3)
-- statement:
--   Bob holds one card $\rho(2)$ and receives Alice's message $M$. His table $B$, with row $M$ and column $\rho(2)$, gives his private result $(y_0, y_1)$, one of the four patterns $0\bullet$, $1\bullet$, $\bullet 0$, $\bullet 1$:
--
--   | $B$ | 0 | 1 | 2 | 3 |
--   |---|---|---|---|---|
--   | X | $0\bullet$ | $1\bullet$ | $\bullet 0$ | $\bullet 1$ |
--   | Y | $0\bullet$ | $\bullet 0$ | $1\bullet$ | $\bullet 1$ |
--   | Z | $0\bullet$ | $\bullet 0$ | $\bullet 1$ | $1\bullet$ |
--
--   The dot marks the bit Bob does not see. The pattern $b\bullet$ (right dot) means that Bob's selection bit is $s = 0$ and he learned $m_0 = b$; the pattern $\bullet b$ (left dot) means $s = 1$ and he learned $m_1 = b$. Every row is a permutation of the four patterns.
--
--   **Formalization Note** An entry is encoded as Bob's oblivious-transfer output $(s, m_s)$, a pair of Booleans with $\texttt{true} = 1$: $b\bullet \mapsto (\texttt{false}, b)$ and $\bullet b \mapsto (\texttt{true}, b)$. This is a bijection between the four printed patterns and the four pairs.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Fig. 3 and the caption of Fig. 5, p.3 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg

set_option autoImplicit false

namespace TetraOT

/-- **Bob's lookup table `B`** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Fig. 3, p.3; p. = PDF page, the PDF has no printed page
numbers). `bobTable M c` is the entry in row `M` and column `ρ(2) = c` of Fig. 3, "Bob lookup table
for incoming message M ∈ {X, Y, Z} with hand ρ(2), giving his private results y₀, y₁". The printed
table:

| B | 0  | 1  | 2  | 3  |
|---|----|----|----|----|
| X | 0• | 1• | •0 | •1 |
| Y | 0• | •0 | 1• | •1 |
| Z | 0• | •0 | •1 | 1• |

An entry is the pair `(y₀, y₁)` with `y_s = m_s` and `y_{1−s} = •` (§3, p.3). Fig. 5's caption (p.3):
"s = 0 is denoted by a right dot, s = 1 by a left dot". So "b•" means s = 0 and m_s = b, and "•b"
means s = 1 and m_s = b.

**Formalization Note.** The entry is encoded as Bob's ROT output `(s, m_s) : Bool × Bool`, with
`true` = 1: "b•" ↦ `(false, b)` and "•b" ↦ `(true, b)`. This map is a bijection from the four patterns
`{0•, 1•, •0, •1}` onto `Bool × Bool`. For example `B(Y, 3) = •1` (Fig. 4) is `(true, true)`. -/
def bobTable : Msg → Fin 4 → Bool × Bool
  | Msg.X => ![(false, false), (false, true), (true, false), (true, true)]
  | Msg.Y => ![(false, false), (true, false), (false, true), (true, true)]
  | Msg.Z => ![(false, false), (true, false), (true, true), (false, true)]

end TetraOT


