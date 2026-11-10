-- Prove2me | Definitions.Def_GreedNorm_glbInitState
-- name    : GreedNorm_glbInitState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:51.447096+00:00
-- url     : https://prove2.me/theorems/da09edd9-aafe-41ab-ad9f-73548e81a480
-- title:
--   Initial machine state on a GLB instance
-- statement:
--   The input of a GLB instance $(n,m,p)$ to the machine: integer memory cell $0$ holds $n$ and cell $1$ holds $m$; real memory holds $p_{ij}$ at address $i\cdot n+j$ ($0\le i<m$, $0\le j<n$) and $0$ at every other address; all registers are $0$. The norms $f_i$ and $g$ are not written in memory: they are the oracles.
--
--   **Formalization Note** The real memory is written as a double sum with at most one nonzero term. The output convention (integer cell $2+j$ holds $\sigma(j)$) is part of the theorem statements.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 1.1, p.1 (PDF 3); Theorem 1.3, p.2 (PDF 4)

import Mathlib
import Definitions.Def_GreedNorm_Machine

namespace GreedNorm

/-- **The initial machine state on a GLB instance** `(n, m, p)`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256
2a3d250c…a300b1b6), Definition 1.1, p.1 (PDF 3), and Theorem 1.3, p.2 (PDF 4).

**Formalization Note** Input layout: integer memory cell `0` holds `n` and cell `1` holds `m`
(all other integer cells `0`); real memory holds `p i j` at address `i * n + j` for `i < m`,
`j < n`, and `0` at every other address (the double sum below has at most one nonzero term,
since `j < n`). The norms are not part of the memory: they are the oracles of
`Machine.innerQuery` / `Machine.outerQuery`. The output convention (integer cell `2 + j` holds
`σ(j)`) is stated in the theorems. -/
noncomputable def glbInitState {n m : ℕ} (p : Fin m → Fin n → ℝ) : Machine.State :=
  Machine.init
    (fun a => ∑ i : Fin m, ∑ j : Fin n, if a = (i : ℤ) * (n : ℤ) + (j : ℤ) then p i j else 0)
    (fun a => if a = 0 then (n : ℤ) else if a = 1 then (m : ℤ) else 0)

end GreedNorm


