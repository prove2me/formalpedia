-- Prove2me | Definitions.Def_TetraOT_Supplement_redBlackAliceTable
-- name    : TetraOT_Supplement_redBlackAliceTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:37:50.56628+00:00
-- url     : https://prove2.me/theorems/14b395fc-e0e7-4a65-bece-5514cd68570a
-- title:
--   Alice's red-black table (Fig. 22)
-- statement:
--   The cards $0,1,2,3$ are relabeled $L0, L1, R0, R1$ (Fig. 20): a card's side is L for $0,1$ and R for $2,3$, and its bit value is $0$ for $0,2$ and $1$ for $1,3$. Alice's red-black table assigns to her two cards either a pair of bits $m_0m_1$ or "reject":
--
--   | left | right | $m_0m_1$ |
--   |---|---|---|
--   | L0 | R0 | 11 |
--   | L0 | R1 | 10 |
--   | L1 | R0 | 01 |
--   | L1 | R1 | 00 |
--   | L0 | L1 | reject |
--   | R0 | R1 | reject |
--
--   So a hand with one L card $\ell$ and one R card $r$ gives $m_0 = 1-\mathrm{bit}(\ell)$ and $m_1 = 1-\mathrm{bit}(r)$, and a hand with both cards on the same side is rejected. The table does not depend on the order of Alice's two cards.
--
--   **Formalization Note** The value is an optional pair of Booleans ($\texttt{true}=1$), with "none" for reject. The diagonal (two equal cards) is never reached by a deal and is set to "none".
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Figs. 20 and 22, p.10 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib

set_option autoImplicit false

namespace TetraOT.Supplement

/-- **Alice's red-black table** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Fig. 22, p.10, with the card labels of Fig. 20,
p.10; p. = PDF page, the PDF has no printed page numbers). Cards are relabeled `0 = L0, 1 = L1,
2 = R0, 3 = R1` (Fig. 20: "Convenient labeling of cards 0-3 as L0-L1-R0-R1"). Fig. 22:

| left | right | m₀m₁   |
|------|-------|--------|
| L0   | R0    | 11     |
| L0   | R1    | 10     |
| L1   | R0    | 01     |
| L1   | R1    | 00     |
| L0   | L1    | reject |
| R0   | R1    | reject |

`redBlackAliceTable a b` is Alice's result on the ordered hand `(ρ(0), ρ(1)) = (a, b)`: `some (m₀, m₁)`
when the hand has one L card and one R card ("Alice basically sorts LR and inverts bits", p.10), and
`none` (reject) when both cards are on the same side.

**Formalization Note.** Bits are `Bool` with `true` = 1. The table ignores the order of Alice's hand
(the columns of Fig. 22 are "left" and "right", not "first" and "second"), so the entries for `(a, b)` and
`(b, a)` agree. The four diagonal cells are not reached by any deal (`ρ(0) ≠ ρ(1)`) and are set to
`none`; any other value gives the same protocol run. -/
def redBlackAliceTable : Fin 4 → Fin 4 → Option (Bool × Bool) :=
  ![![none, none, some (true, true), some (true, false)],
    ![none, none, some (false, true), some (false, false)],
    ![some (true, true), some (false, true), none, none],
    ![some (true, false), some (false, false), none, none]]

end TetraOT.Supplement


