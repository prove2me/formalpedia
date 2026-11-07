-- Prove2me | Definitions.Def_ShallowSym_pairFn
-- name    : ShallowSym_pairFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:49.602828+00:00
-- url     : https://prove2.me/theorems/98999b3d-a561-4000-9c44-91d77a688a25
-- title:
--   The pair function $1[w_i+s_i\not\equiv w_j+s_j \pmod k]$
-- statement:
--   Fix a partition $\beta$ into $k$ blocks and shifts $s_0,\dots,s_{k-1}\in\mathbb Z/k\mathbb Z$. For two blocks $i,j$ the **pair function** is
--
--   $$x\ \mapsto\ 1\big[\,w_i(x)+s_i \not\equiv w_j(x)+s_j \pmod k\,\big].$$
--
--   A test is the AND of these functions over all pairs $i<j$ (eqs. (3) and (5)); each pair function depends only on the variables of blocks $i$ and $j$.
--
--   **Formalization Note** Shifts are elements of `ZMod k` and the comparison is in `ZMod k`.
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §3 eq. (3), p.8; §4 eq. (5), p.11

import Mathlib
import Definitions.Def_ShallowSym_blockWeight

namespace ShallowSym

/-- The pair function `1[w_i + s_i ≢ w_j + s_j (mod k)]` of a test: for a partition
`β : Fin n → Fin k` into blocks and shifts `s : Fin k → ZMod k`, it is true at `x` exactly when
the shifted block weights of blocks `i` and `j` differ modulo `k`.

V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…), §3 eq. (3), p.8 and §4 eq. (5), p.11: "the constituent functions
1[wi + si ≢ wj + sj (mod k)]".

**Formalization Note.** Shifts are elements of `ZMod k` (the paper's {0, 1, …, k − 1}), and the
comparison is in `ZMod k`, i.e. modulo `k`. -/
def pairFn {n k : ℕ} (β : Fin n → Fin k) (s : Fin k → ZMod k) (i j : Fin k) (x : Cube n) :
    Bool :=
  decide (((blockWeight β x i : ℕ) : ZMod k) + s i ≠ ((blockWeight β x j : ℕ) : ZMod k) + s j)

end ShallowSym


