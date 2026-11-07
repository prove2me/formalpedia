-- Prove2me | Definitions.Def_MemoryRegret_sgn
-- name    : MemoryRegret_sgn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:25.727637+00:00
-- url     : https://prove2.me/theorems/1f18c7e8-77f6-4ffa-9267-93159effcbc2
-- title:
--   The sign map $b\mapsto(-1)^b$ on labels
-- statement:
--   Labels $\{0,1\}$ are booleans with $\mathtt{false}=0$ and $\mathtt{true}=1$, and $\mathrm{sgn}(b)=(-1)^b$. Thus $(-1)^{a+b}=\mathrm{sgn}(a)\,\mathrm{sgn}(b)$, and the matrix of a hypothesis class is $M(x,h)=\mathrm{sgn}(h(x))$.
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), §2, p.7

import Mathlib

namespace MemoryRegret

/-- **The sign map `b ↦ (−1)^b` on labels.**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
§2, p.7: "we define a matrix M : X × H → {−1, 1} as follows: for all, x ∈ X and h ∈ H,
M(x, h) = (−1)^{h(x)}".

**Formalization Note.** Labels in `{0, 1}` are `Bool`, with `false = 0` and `true = 1`, so
`sgn false = 1 = (−1)^0` and `sgn true = −1 = (−1)^1`; hence
`(−1)^{a+b} = sgn a * sgn b`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

end MemoryRegret


