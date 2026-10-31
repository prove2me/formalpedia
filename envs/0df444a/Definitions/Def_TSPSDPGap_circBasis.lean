-- Prove2me | Definitions.Def_TSPSDPGap_circBasis
-- name    : TSPSDPGap_circBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:05.071305+00:00
-- url     : https://prove2.me/theorems/c9c0ad8a-26b8-4d2b-a1c6-58a8b7753f7c
-- title:
--   Basis of symmetric circulant matrices $C^{(m)}_i$
-- statement:
--   A **circulant matrix** in $\mathbb R^{m\times m}$ has the entry $c_{(t-s)\bmod m}$ in row $s$ and column $t$. The **standard basis of symmetric circulant matrices** consists of $C^{(m)}_0, C^{(m)}_1,\dots$, where for $0<i<m/2$ the matrix $C^{(m)}_i$ has $c_i=c_{m-i}=1$ and $c_j=0$ otherwise, $C^{(m)}_0=2I$, and, for even $m$, $C^{(m)}_{m/2}$ has $c_{m/2}=2$ and $c_j=0$ otherwise. In one formula,
--   $$
--   \bigl(C^{(m)}_i\bigr)_{st}=\mathbb 1\{t-s\equiv i \pmod m\}+\mathbb 1\{s-t\equiv i \pmod m\}.
--   $$
--   Every row of $C^{(m)}_i$ sums to $2$, and $C^{(m)}_1$ is the adjacency matrix of the cycle on $m\ge3$ vertices in their natural order.
--
--   These matrices carry the objective of both SDP relaxations (through $C_1$) and build the circulant blocks $A$ and $B$ of the feasible solution (3).
--
--   **Formalization Note** Rows and columns are indexed by `Fin m` (0-based). For $i>m$ the formula returns the matrix of $i \bmod m$; the paper only uses $0\le i\le m/2$.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, §2.1, p.5

import Mathlib

namespace TSPSDPGap

/-- **The basis of symmetric circulant matrices `C^{(m)}_i`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, §2.1, p.5: "We use a standard basis of symmetric circulant matrices in
R^{m×m} consisting of matrices C^{(m)}_0, C^{(m)}_1, ..., C^{(m)}_d where, for i = 1, ..., d − 1,
C^{(m)}_i is the symmetric circulant m × m matrix with c_i = c_{m−i} = 1 and c_j = 0 otherwise.
We set C^m_0 = 2I and, when m is even, set C^{(m)}_{m/2} to be the matrix where c_{m/2} = 2 and
c_j = 0 otherwise." A circulant matrix has entry `c_{(t−s) mod m}` in row `s`, column `t` (p.5).

The entry of `circBasis m i` in row `s`, column `t` is
`[t − s ≡ i (mod m)] + [s − t ≡ i (mod m)]`.

**Formalization Note.** Rows and columns are `Fin m` (0-based: the paper's index `1` is `0`).
The single formula gives all three printed cases: `c_i = c_{m−i} = 1` for `0 < i < m/2`,
`C_0 = 2I`, and `c_{m/2} = 2` when `m` is even. The paper uses the basis only for
`0 ≤ i ≤ m/2`; for larger `i` the formula is the matrix of `i mod m`. `circBasis m 1` is the
adjacency matrix of the cycle `0, 1, …, m − 1` for `m ≥ 3`. -/
def circBasis (m i : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun s t =>
    (if ((t : ℕ) + m - s) % m = i % m then 1 else 0) +
      (if ((s : ℕ) + m - t) % m = i % m then 1 else 0)

end TSPSDPGap


