-- Prove2me | Definitions.Def_TetraOT_Supplement_bobInvTable
-- name    : TetraOT_Supplement_bobInvTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:36:04.817012+00:00
-- url     : https://prove2.me/theorems/1732ac4f-2565-4940-9e7e-18a6eb8b2814
-- title:
--   Bob's inverse lookup table $B^{-1}(M, y_0y_1)$ (Fig. 8)
-- statement:
--   In the inverted Tetrahedral Protocol Bob receives Alice's message $M\in\{X,Y,Z\}$ and the output $(y_0,y_1)$ of one random 1-of-2 oblivious transfer, one of the four patterns $0\bullet, 1\bullet, \bullet 0, \bullet 1$. His inverse table $B^{-1}$ turns this pair into a card $\rho(2)\in\{0,1,2,3\}$:
--
--   | $B^{-1}$ | $\bullet 0$ | $\bullet 1$ | $0\bullet$ | $1\bullet$ |
--   |---|---|---|---|---|
--   | X | 2 | 3 | 0 | 1 |
--   | Y | 1 | 3 | 0 | 2 |
--   | Z | 1 | 2 | 0 | 3 |
--
--   Every row of Bob's forward table $B$ (Fig. 3) is a permutation of the four patterns, and $B^{-1}$ is its row-wise inverse: $B^{-1}(M, B(M,c)) = c$ for every message $M$ and card $c$.
--
--   **Formalization Note** A pattern is encoded as Bob's oblivious-transfer output $(s, m_s)$ with bits as Booleans ($\texttt{true}=1$), as in the published table $B$: "$b\bullet$" is $(0,b)$ and "$\bullet b$" is $(1,b)$. The table is transcribed from Fig. 8, not obtained by inverting $B$ with a choice function.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Fig. 8, p.4 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg

set_option autoImplicit false

namespace TetraOT.Supplement

open TetraOT

/-- **Bob's inverse lookup table `B⁻¹`** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Fig. 8, p.4; p. = PDF page, the PDF has no printed
page numbers): "Bob inverse lookup table for incoming message M ∈ {X, Y, Z} with OT results m₀m₁,
giving his effective ρ(2)". `bobInvTable M y` is the entry in row `M` and column `y` of Fig. 8:

| B⁻¹ | •0 | •1 | 0• | 1• |
|-----|----|----|----|----|
| X   | 2  | 3  | 0  | 1  |
| Y   | 1  | 3  | 0  | 2  |
| Z   | 1  | 2  | 0  | 3  |

It is used in the inverted Tetrahedral Protocol (Fig. 10, p.5): Bob receives `(y₀, y₁)` from the
½ROT channel and sets `ρ(2) ← B⁻¹(M, y₀y₁)`.

**Formalization Note.** The OT result `(y₀, y₁)` is encoded as Bob's ROT output `(s, m_s) : Bool × Bool`
with `true` = 1, exactly as in the published `TetraOT.bobTable` (Fig. 5 caption, p.3): "b•" ↦ `(false, b)`
and "•b" ↦ `(true, b)`. So the columns `•0, •1, 0•, 1•` are `(true, false), (true, true), (false, false),
(false, true)`. The table is transcribed from Fig. 8, not obtained by inverting `bobTable` with a choice
function; every row of Fig. 3 is a permutation of the four patterns, and Fig. 8 is its row-wise inverse. -/
def bobInvTable : Msg → Bool × Bool → Fin 4
  | Msg.X, (true, false) => 2
  | Msg.X, (true, true) => 3
  | Msg.X, (false, false) => 0
  | Msg.X, (false, true) => 1
  | Msg.Y, (true, false) => 1
  | Msg.Y, (true, true) => 3
  | Msg.Y, (false, false) => 0
  | Msg.Y, (false, true) => 2
  | Msg.Z, (true, false) => 1
  | Msg.Z, (true, true) => 2
  | Msg.Z, (false, false) => 0
  | Msg.Z, (false, true) => 3

end TetraOT.Supplement


