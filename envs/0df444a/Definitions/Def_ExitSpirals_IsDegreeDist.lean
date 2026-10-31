-- Prove2me | Definitions.Def_ExitSpirals_IsDegreeDist
-- name    : ExitSpirals_IsDegreeDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:17.622551+00:00
-- url     : https://prove2.me/theorems/d6a09c02-7215-4f0c-a1e5-80853bbf04bb
-- title:
--   Joint in/out-degree distribution $p_{jk}$ with mean degree $\lambda\in(0,\infty)$
-- statement:
--   A **joint degree distribution** is a family $(p_{jk})_{j,k\ge0}$ of nonnegative numbers summing to $1$, where $p_{jk}$ is the fraction of agents with **in-degree $j$ and out-degree $k$**. It satisfies Assumption A.1(2) if both mean sums converge and agree,
--   $$\lambda=\sum_{j,k}j\,p_{jk}=\sum_{j,k}k\,p_{jk}\in(0,\infty),$$
--   so that in aggregate the in-links match the out-links. `meanDeg p` is $\lambda$.
--
--   These laws are the parameters of the random networks: each market $\mu\in\{R,C\}$ has its own $p_{jk,\mu}$, and every threshold of the paper is a function of them.
--
--   **Formalization Note** $j$ is the in-degree, as on pp.16 and 25; Appendix A.3 prints the empirical law with the opposite order, which is not followed. No second-moment condition is part of this definition: Assumption A.1(3) is a condition on the degree sequences.
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), §3.2, p.16 and §4.3.1, p.25 (p_jk with j the in-degree); Assumption A.1(2), p.48

import Mathlib

namespace ExitSpirals

/-- **Mean degree** `λ = Σ_{j,k} p_{jk} j` of a joint degree distribution (Assumption A.1(2),
p.48). Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814.

**Formalization Note.** `p j k` is the fraction of agents with **in**-degree `j` and
**out**-degree `k`, the convention of pp.16 and 25 (Appendix A.3, p.47, prints the empirical
`p_{jk,n}` with `j` the out-degree; see `IsDegreeDist`). -/
noncomputable def meanDeg (p : ℕ → ℕ → ℝ) : ℝ :=
  ∑' jk : ℕ × ℕ, (jk.1 : ℝ) * p jk.1 jk.2

/-- **Joint degree distribution** `(p_{jk})_{j,k ≥ 0}` with Assumption A.1(2).
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, §3.2, p.16
("p_{jk,µ} is the fraction of agents with in-degree j and out-degree k"), §4.3.1, p.25, and
Assumption A.1(2), p.48: "λ := Σ_{j,k} p_{jk} j = Σ_{j,k} p_{jk} k ∈ (0, ∞)".

`IsDegreeDist p` says: `p ≥ 0`, `p` sums to `1` over `ℕ × ℕ`, both mean sums converge, they are
equal, and their common value `λ = meanDeg p` is positive.

**Formalization Note.** `j` is the in-degree and `k` the out-degree (pp.16, 25), not A.3's
printed order. No second-moment condition is part of this definition: A.1(3) is a condition on
the degree sequences (`WellBehaved`). -/
def IsDegreeDist (p : ℕ → ℕ → ℝ) : Prop :=
  (∀ j k, 0 ≤ p j k) ∧
  HasSum (fun jk : ℕ × ℕ => p jk.1 jk.2) 1 ∧
  Summable (fun jk : ℕ × ℕ => (jk.1 : ℝ) * p jk.1 jk.2) ∧
  Summable (fun jk : ℕ × ℕ => (jk.2 : ℝ) * p jk.1 jk.2) ∧
  ∑' jk : ℕ × ℕ, (jk.2 : ℝ) * p jk.1 jk.2 = meanDeg p ∧
  0 < meanDeg p

end ExitSpirals


