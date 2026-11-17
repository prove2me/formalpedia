-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_deltaOrth
-- name    : AvgCaseTI_Supplement_deltaOrth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:32:30.245205+00:00
-- url     : https://prove2.me/theorems/3edca0b9-e813-4190-9335-3fbad6d13cd3
-- title:
--   The Gram-matrix comparison error $\delta_{n,q}$
-- statement:
--   For a prime power $q$ and $n\ge2$,
--   $$
--   \delta_{n,q}:=\frac12\left(\frac{q^{-n(n-1)}}{c(q)\bigl(1-q^{-n(n-1)}\bigr)}\right)^{1/2},
--   $$
--   where $c(q)=\prod_{i\ge1}(1-q^{-i})$. It bounds the total variation distance between the Gram matrix $M_AM_A^t$ of a uniform $n\times n^2$ matrix and a uniform symmetric matrix (Proposition 5.2), and it is one of the three error terms of Theorem 5.6.
--
--   **Formalization Note** $c(q)$ is the published `cInf`; the square root is the real square root.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 5.2, Eq. (30), p.32 (PDF p.34)

import Mathlib
import Definitions.Def_AvgCaseTI_cn

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI

/-- **The Gram-matrix comparison error `δ_{n,q}`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 5.2, Eq. (30), p.32 (PDF p.34):
"δ_{n,q} := ½ (q^{−n(n−1)} / (c(q)(1 − q^{−n(n−1)})))^{1/2}".

`deltaOrth q n = ½ · √(q^{−n(n−1)} / (c(q) · (1 − q^{−n(n−1)})))`, with `c(q) = cInf q`.

**Formalization Note.** Only odd `q ≥ 3` and `n ≥ 3` are used, where the radicand is positive. -/
noncomputable def deltaOrth (q : ℝ) (n : ℕ) : ℝ :=
  1 / 2 * Real.sqrt (q ^ (-((n : ℤ) * ((n : ℤ) - 1))) /
    (cInf q * (1 - q ^ (-((n : ℤ) * ((n : ℤ) - 1))))))

end AvgCaseTI.Supplement


