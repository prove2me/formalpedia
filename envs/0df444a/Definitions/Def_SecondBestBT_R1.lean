-- Prove2me | Definitions.Def_SecondBestBT_R1
-- name    : SecondBestBT_R1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:20.112949+00:00
-- url     : https://prove2.me/theorems/89fd7bae-e405-45a5-9a83-398ba7f597dc
-- title:
--   Allocation class $R_1(W)$: monotone interims
-- statement:
--   For priors $f_S,f_B$ on $Z_W$,
--   $$
--   R_1(W)=\Big\{x:Z_W^2\to[0,1]\ :\ x_B(b)\le x_B(b')\ \text{for all } b<b',\ \ x_S(s)\ge x_S(s')\ \text{for all } s<s'\Big\},
--   $$
--   where $x_B(b)=\sum_s f_S(s)x(s,b)$ and $x_S(s)=\sum_b f_B(b)x(s,b)$. The class depends on the priors.
--
--   **Formalization Note** An allocation is a matrix `ℕ → ℕ → ℝ`; entries with an index above $W$ are unconstrained and unused.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 4.1, p.8

import Mathlib
import Definitions.Def_SecondBestBT_gridInterimB
import Definitions.Def_SecondBestBT_gridInterimS

namespace SecondBestBT

/-- The allocation class `R1(W)` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256
17184930…, Section 4.1, p.8): allocations `x : Z_W² → [0, 1]` whose interim allocations are
monotone, `x_B(b) ≤ x_B(b')` for all `b < b'` and `x_S(s) ≥ x_S(s')` for all `s < s'`, with
`x_B(b) = ∑_s f_S(s) x(s, b)` and `x_S(s) = ∑_b f_B(b) x(s, b)`.

**Formalization Note** The class depends on the priors through the interims. Entries of the matrix
with an index above `W` are unconstrained and unused. -/
def R1 (fS fB : ℕ → ℝ) (W : ℕ) : Set (ℕ → ℕ → ℝ) :=
  {x | (∀ s ≤ W, ∀ b ≤ W, x s b ∈ Set.Icc (0 : ℝ) 1) ∧
    MonotoneOn (gridInterimB fS W x) (Set.Iic W) ∧
    AntitoneOn (gridInterimS fB W x) (Set.Iic W)}

end SecondBestBT


