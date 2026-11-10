-- Prove2me | Definitions.Def_TetraOT_aliceTable
-- name    : TetraOT_aliceTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:44.19931+00:00
-- url     : https://prove2.me/theorems/b84c7792-e9c9-447b-b6d8-ef12d237c7e2
-- title:
--   Alice's lookup table $A(\rho(0),\rho(1)) = (M, m_0 m_1)$ (Fig. 2)
-- statement:
--   Alice holds the ordered pair of cards $(\rho(0), \rho(1))$ from a 4-card deck $\{0,1,2,3\}$. Her table $A$ assigns to it a message $M\in\{X,Y,Z\}$ and two private bits $m_0, m_1$. The row is $\rho(0)$, the column is $\rho(1)$, and an entry "$M\ m_0m_1$" lists the message followed by the two bits:
--
--   | $A$ | 0 | 1 | 2 | 3 |
--   |---|---|---|---|---|
--   | 0 | $\cdot$ | Z 11 | X 11 | Y 10 |
--   | 1 | Y 11 | $\cdot$ | Y 01 | X 00 |
--   | 2 | Z 10 | X 01 | $\cdot$ | Z 00 |
--   | 3 | X 10 | Z 01 | Y 00 | $\cdot$ |
--
--   Each of the 12 ordered hands gets one of the 12 pairs $(M, m_0m_1)$, each pair exactly once. The table is not symmetric: $A(0,1) = Z\,11$ while $A(1,0) = Y\,11$, so the order of Alice's two cards matters.
--
--   **Formalization Note** Bits are Booleans with $\texttt{true} = 1$. The diagonal cells, printed "$\cdot$", are never reached because a deal gives Alice two different cards; the Lean function needs a value there and uses the fixed value $(X, 00)$, which does not affect any run of the protocol.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Fig. 2, p.3 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg

set_option autoImplicit false

namespace TetraOT

/-- **Alice's lookup table `A`** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Fig. 2, p.3; p. = PDF page, the PDF has no printed
page numbers). `aliceTable a b = (M, (m₀, m₁))` is the entry in row `ρ(0) = a` and column `ρ(1) = b`
of Fig. 2, "Alice's lookup table for hand (ρ(0), ρ(1)), giving message M ∈ {X, Y, Z} and private bits
m₀, m₁". The printed table, with `m₀m₁` written as two digits:

| A | 0    | 1    | 2    | 3    |
|---|------|------|------|------|
| 0 | ⋅    | Z 11 | X 11 | Y 10 |
| 1 | Y 11 | ⋅    | Y 01 | X 00 |
| 2 | Z 10 | X 01 | ⋅    | Z 00 |
| 3 | X 10 | Z 01 | Y 00 | ⋅    |

**Formalization Note.** Bits are `Bool` with `true` = 1, so `Z 10` is `(Msg.Z, (true, false))`
(m₀ = 1, m₁ = 0). The row is Alice's first card `ρ(0)` and the column her second card `ρ(1)`; the
table is not symmetric (`A(0,1) = Z 11`, `A(1,0) = Y 11`), so the order of the hand matters. The four
diagonal cells are printed "⋅": no deal reaches them, because `ρ(0) ≠ ρ(1)` for a permutation `ρ`.
A total Lean function needs a value there; the fixed value `(Msg.X, (false, false))` is used, and
any other value gives the same protocol run. -/
def aliceTable : Fin 4 → Fin 4 → Msg × (Bool × Bool) :=
  ![![(Msg.X, (false, false)), (Msg.Z, (true, true)), (Msg.X, (true, true)), (Msg.Y, (true, false))],
    ![(Msg.Y, (true, true)), (Msg.X, (false, false)), (Msg.Y, (false, true)), (Msg.X, (false, false))],
    ![(Msg.Z, (true, false)), (Msg.X, (false, true)), (Msg.X, (false, false)), (Msg.Z, (false, false))],
    ![(Msg.X, (true, false)), (Msg.Z, (false, true)), (Msg.Y, (false, false)), (Msg.X, (false, false))]]

end TetraOT


