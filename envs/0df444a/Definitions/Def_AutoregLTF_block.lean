-- Prove2me | Definitions.Def_AutoregLTF_block
-- name    : AutoregLTF_block
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:21.176938+00:00
-- url     : https://prove2.me/theorems/1b3680fb-c028-4c49-a645-da64d728c294
-- title:
--   The block length $p=378(m+2)$, positions $\pi$, and blocks $E^t_{\theta,i}$, (13)–(15)
-- statement:
--   Let $p=378(m+2)$ (13). Within a block of $p$ bits, numbered $0,\dots,p-1$, the positions (14) are
--
--   $$\pi(\mathrm{test})=\tfrac p6+3,\quad \pi(\mathrm{row},j)=\tfrac p6+63j+6,\quad \pi(\mathrm{out},j)=\tfrac p6+63j+15\quad(j\in[m]),$$
--   $$\pi(\mathrm{ptr},j)=\tfrac p6+63j+45+6(j\bmod 2)\quad(j\in[m+1]).$$
--
--   The block $E^t_{\theta,i}\in\{0,1\}^p$ (15) has $E_0=1$, the row bit $f^t_{\theta,i,\mathrm{row},j}$ at $\pi(\mathrm{row},j)$, each test, output and pointer bit $f^t_{\theta,i,b}$ at both $\pi(b)$ and $\pi(b)+1$, and zeros elsewhere.
--
--   Blocks are the unit that one autoregressive LTF rewrites per $p$ steps.
--
--   **Formalization Note** `p m / 6` is $p/6=63(m+2)$ exactly. A block is `ℕ → Bool`, written as a Boolean disjunction over the listed positions; these are distinct (p.7) and below $p/3$, so this is the paper's block and it is `false` at every $r\ge p$.
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §3, (13)–(15), pp.7–8

import Mathlib
import Definitions.Def_AutoregLTF_state

namespace AutoregLTF

/-!
# Block length `p`, positions `π`, and the blocks `E^t_{θ,i}`, (13)–(15)

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §3, (13)–(15),
pp.7–8.

`p = 378(m + 2)`; the positions within a block of length `p` (numbered `0, …, p − 1`) are
`π(test) = p/6 + 3`, `π(row, j) = p/6 + 63j + 6`, `π(out, j) = p/6 + 63j + 15` (`j ∈ [m]`) and
`π(ptr, j) = p/6 + 63j + 45 + 6(j mod 2)` (`j ∈ [m + 1]`). The block `E^t_{θ,i} ∈ {0,1}^p` has
`E_0 = 1`, the row bit `f^t_{row,j}` at `π(row, j)`, each test, output and pointer bit at both `π(b)`
and `π(b) + 1`, and zeros at all other positions.

**Formalization Note.**
* Positions are natural numbers; `p/6 = 63(m + 2)` exactly, so `p m / 6` is the paper's `p/6`.
* A block is `ℕ → Bool`, read at positions `0 ≤ r < p`. It is written as a Boolean disjunction over
  the positions of (15); `List.range' 1 m` is `[1, …, m]`. The paper notes (p.7) that these positions
  are distinct, so the disjunction is the paper's assignment "and set all other positions to zero". Every listed position is below `p/3`, so
  the block is `false` at every `r ≥ p`.
-/

/-- The block length `p = 378(m + 2)`, (13). -/
def p (m : ℕ) : ℕ := 378 * (m + 2)

/-- `π(test) = p/6 + 3`, (14). -/
def piTest (m : ℕ) : ℕ := p m / 6 + 3

/-- `π(row, j) = p/6 + 63j + 6`, (14). -/
def piRow (m j : ℕ) : ℕ := p m / 6 + 63 * j + 6

/-- `π(out, j) = p/6 + 63j + 15`, (14). -/
def piOut (m j : ℕ) : ℕ := p m / 6 + 63 * j + 15

/-- `π(ptr, j) = p/6 + 63j + 45 + 6(j mod 2)`, (14). -/
def piPtr (m j : ℕ) : ℕ := p m / 6 + 63 * j + 45 + 6 * (j % 2)

/-- The block (15) encoding a state `f`: position `0` is `1`; `π(row, j)` holds `f_{row,j}`
(`j ∈ [m]`); `π(test)` and `π(test) + 1` hold `f_{test}`; `π(out, j)`, `π(out, j) + 1` hold
`f_{out,j}` (`j ∈ [m]`); `π(ptr, j)`, `π(ptr, j) + 1` hold `f_{ptr,j}` (`j ∈ [m + 1]`); every other
position is `0`. -/
def block (m : ℕ) (f : St) (r : ℕ) : Bool :=
  decide (r = 0) ||
    (List.range' 1 m).any (fun j => decide (r = piRow m j) && f.row j) ||
    ((decide (r = piTest m) || decide (r = piTest m + 1)) && f.test) ||
    (List.range' 1 m).any
      (fun j => (decide (r = piOut m j) || decide (r = piOut m j + 1)) && f.out j) ||
    (List.range' 1 (m + 1)).any
      (fun j => (decide (r = piPtr m j) || decide (r = piPtr m j + 1)) && f.ptr j)

/-- The block `E^t_{θ,i}` of (15): the encoding of the state `f^t_{θ,i}`. -/
def E (m : ℕ) (θ : ℕ → ℤ) (i t : ℕ) : ℕ → Bool :=
  block m (state m θ i t)

end AutoregLTF


