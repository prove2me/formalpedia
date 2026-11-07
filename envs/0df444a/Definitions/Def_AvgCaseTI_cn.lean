-- Prove2me | Definitions.Def_AvgCaseTI_cn
-- name    : AvgCaseTI_cn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:24.950397+00:00
-- url     : https://prove2.me/theorems/65822078-6bb8-4545-942a-d8ef8342bc81
-- title:
--   The ratio $c_n(q)=\prod_{i=1}^n(1-q^{-i})$ and its limit $c(q)$
-- statement:
--   For $q>1$ and $n\ge0$ put
--   $$
--   c_n(q)=\prod_{i=1}^{n}\bigl(1-q^{-i}\bigr),\qquad c(q)=\lim_{n\to\infty}c_n(q)=\prod_{i=1}^{\infty}\bigl(1-q^{-i}\bigr),
--   $$
--   and, for the tail of the infinite product, $\prod_{i=n+1}^{\infty}(1-q^{-i})$. For a prime power $q$, $c_n(q)=|\mathrm{GL}(n,q)|/|\mathrm M(n,q)|$ is the probability that a uniform $n\times n$ matrix over $\mathbb F_q$ is invertible, and $c(q)$ its limit; these constants express every limiting probability of the mission.
--
--   **Formalization Note** `cn q n` is the finite product ($c_0(q)=1$). The partial products are positive and decreasing when $q>1$, so their limit is their infimum: `cInf q` $=\inf_n c_n(q)$ and `tailProd q n` $=\inf_m\prod_{i=n+1}^{n+m}(1-q^{-i})$. No unconditioned infinite product is used.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 2.1, Eqs. (2)–(3), p.13 (PDF p.15)

import Mathlib

set_option autoImplicit false

namespace AvgCaseTI

/-- **The ratio `c_n(q) = |GL(n,q)| / |M(n,q)| = ∏_{i=1}^{n} (1 − q^{−i})`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 2.1, Eq. (2),
p.13 (PDF p.15).

`cn q n = ∏_{i=0}^{n−1} (1 − q^{−(i+1)})`; `cn q 0 = 1`.

**Formalization Note.** Defined by the product formula for every real `q`; only `q ≥ 2` is used. -/
noncomputable def cn (q : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (1 - q ^ (-((i : ℤ) + 1)))

/-- **The constant `c(q) = lim_{n→∞} c_n(q) = ∏_{i≥1} (1 − q^{−i})`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 2.1, p.13
(PDF p.15): "converges to a constant c(q) := lim_{n→∞} c_n(q)".

**Formalization Note.** For `q > 1` the partial products `c_n(q)` are positive and decrease, so their
limit is their infimum; `cInf q` is that infimum (never an unconditioned `tprod`). For `q ≤ 1` the
value is not used. -/
noncomputable def cInf (q : ℝ) : ℝ := ⨅ n : ℕ, cn q n

/-- **The tail product `∏_{i=n+1}^{∞} (1 − q^{−i})`** of Eq. (3), p.13 (PDF p.15), as the infimum
of its partial products `∏_{i=n+1}^{n+m} (1 − q^{−i})` (decreasing and positive for `q > 1`). -/
noncomputable def tailProd (q : ℝ) (n : ℕ) : ℝ :=
  ⨅ m : ℕ, ∏ i ∈ Finset.range m, (1 - q ^ (-((n : ℤ) + 1 + i)))

end AvgCaseTI


