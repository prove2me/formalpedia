-- Prove2me | Definitions.Def_MemQueryFeas_leafOf
-- name    : MemQueryFeas_leafOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:40.787671+00:00
-- url     : https://prove2.me/theorems/ecc78882-ebdd-4e5d-a792-70e77aea9ed9
-- title:
--   Leaves in lexicographic order
-- statement:
--   The leaves $V_P=[N_1]\times\dots\times[N_P]$ are ordered lexicographically; the $n$-th leaf ($n=0,1,\dots,N_1\cdots N_P-1$) has as coordinates the mixed-radix digits of $n$ for the radices $N_1,\dots,N_P$ (last coordinate least significant), each increased by one. The successor of the $n$-th leaf is the $(n+1)$-th.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.1, p.8 (PDF p.9)

import Mathlib

namespace MemQueryFeas

/-- **The leaves in lexicographic order.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1, p.8 (PDF p.9): "We now focus on leaves `V_P`
which we order lexicographically. … `Succ(l) = min_{≤lex} {l' ∈ V_P : l <lex l'}`."

`leafOf N P n` is the `n`-th leaf (0-based) of `V_P = [N_1] × ⋯ × [N_P]` in lexicographic order: the
mixed-radix digits of `n` with radices `N_1, …, N_P` (last coordinate least significant), each
shifted by `+1`. The successor of the `n`-th leaf is the `(n+1)`-th.

**Formalization Note.** Only `n < ∏_p N_p` (`numLeaves`) names a leaf; the transform oracle never
uses other values. -/
def leafOf (N : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | P + 1, n => leafOf N P (n / N (P + 1)) ++ [n % N (P + 1) + 1]

end MemQueryFeas


