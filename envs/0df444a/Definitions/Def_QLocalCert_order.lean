-- Prove2me | Definitions.Def_QLocalCert_order
-- name    : QLocalCert_order
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:00.966208+00:00
-- url     : https://prove2.me/theorems/9c983d37-5303-4a26-881d-d0a6cc5e6dcd
-- title:
--   The order $n_\mu(N)$ of $T^{\mathrm{tr}}_{N,\mu}(z,z')$
-- statement:
--   With $m=N/2$, $L=\lceil\log_2(N/2+1)\rceil$, $B_L=L(L+1)/2$ and $\mathrm{wt}(i)$ the Hamming weight of the binary expansion of $i$,
--   $$
--   n_\mu(N)=2\Big[1+m+(m+1)(3+B_L)+2\sum_{i=0}^{m}\mathrm{wt}(i)\Big]+2\mu .
--   $$
--   This is the exact count of the vertices of $T^{\mathrm{tr}}_{N,\mu}(z,z')$ given in the proof of Fact 1 (with $\rho-1=2\mu$): each side has its hub, $m+1$ vertices $a_i$, $m$ pendant leaves and the tags, $|\mathrm{Tag}(i)|=2+B_L+2\,\mathrm{wt}(i)$. For $\mu=1$, $N=8$ it is $122$.
--
--   It indexes the instance sizes at which $\mathrm{TreeEQ}_\mu$ has members, which is where the lower bound of Theorem 29 is stated.
--
--   **Formalization Note** `hammingWt i` is the digit sum of `Nat.digits 2 i`. That this number equals the vertex count is milestone Fact 1, not part of the definition.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), proof of Fact 1, p.35

import Mathlib
import Definitions.Def_QLocalCert_Tag

set_option autoImplicit false

namespace QLocalCert

/-- `wt(i)`, the Hamming weight of the binary expansion of `i` (proof of Fact 1, p.35). -/
def hammingWt (i : ℕ) : ℕ := (Nat.digits 2 i).sum

/-- The order `n_µ(N)` of `T^tr_{N,µ}(z, z′)`, by the exact count in the proof of Fact 1 (p.35):
with `m := N/2`, `B_L := L(L+1)/2`,
`n_µ(N) = 2 [1 + m + (m + 1)(3 + B_L) + 2 ∑_{i=0}^{m} wt(i)] + ρ − 1`, and `ρ − 1 = 2µ`.

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), proof of Fact 1, p.35.

**Formalization Note.** `L = tagL N = ⌈log₂(N/2 + 1)⌉`. The division `L(L+1)/2` is exact.
That this number is the vertex count of the tree is part of milestone Fact 1, not of the
definition. For `µ = 1`, `N = 8` it is `122`. -/
def order (μ N : ℕ) : ℕ :=
  2 * (1 + N / 2 + (N / 2 + 1) * (3 + tagL N * (tagL N + 1) / 2)
    + 2 * ∑ i ∈ Finset.range (N / 2 + 1), hammingWt i) + 2 * μ

end QLocalCert


