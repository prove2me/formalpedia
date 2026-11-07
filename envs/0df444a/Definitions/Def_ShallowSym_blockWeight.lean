-- Prove2me | Definitions.Def_ShallowSym_blockWeight
-- name    : ShallowSym_blockWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:09.732206+00:00
-- url     : https://prove2.me/theorems/253b5b5f-ad7c-4077-ae12-802cd67cb31e
-- title:
--   Block weights $w_i(x)$ of a partition into $k$ blocks
-- statement:
--   A partition of the $n$ input coordinates into $k$ blocks is a map $\beta:\{0,\dots,n-1\}\to\{0,\dots,k-1\}$; block $i$ is $B_i=\beta^{-1}(i)$. The **weight of block $i$** at $x\in\{0,1\}^n$ is
--
--   $$w_i(x) = \#\{\, j : \beta(j)=i,\ x_j = 1 \,\}.$$
--
--   Every test of the paper's construction splits the input into blocks and looks at the block weights.
--
--   **Formalization Note** Blocks are indexed from $0$ (`Fin k`). The paper's blocks have length at most $\lceil n/k\rceil$; that bound only matters for sizes and is not part of the definition, so blocks are arbitrary (possibly empty, not necessarily contiguous).
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §3 'Anatomy of a test', p.8; §4, p.11

import Mathlib
import Definitions.Def_ShallowSym_weight

namespace ShallowSym

/-- Block weights. A partition of the `n` input coordinates into `k` blocks is a map
`β : Fin n → Fin k` (block `i` is `β⁻¹(i)`; blocks may be empty and need not be contiguous).
The weight of block `i` at `x` is `w_i(x) = #{j | β j = i ∧ x j = 1}`.

V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…), §3 p.8 and §4 p.11: "each test splits the input x into k blocks of length at most ⌈n/k⌉
… Let wi be the weight of block i."

**Formalization Note.** Blocks are indexed from 0 (`Fin k`), the paper's blocks `1, …, k`.
The length bound ⌈n/k⌉ only matters for circuit sizes and is not part of the definition. -/
def blockWeight {n k : ℕ} (β : Fin n → Fin k) (x : Cube n) (i : Fin k) : ℕ :=
  (Finset.univ.filter (fun j => β j = i ∧ x j = true)).card

end ShallowSym


