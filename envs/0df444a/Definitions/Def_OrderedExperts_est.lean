-- Prove2me | Definitions.Def_OrderedExperts_est
-- name    : OrderedExperts_est
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:38.699773+00:00
-- url     : https://prove2.me/theorems/191f2a38-0d77-44fa-badb-4e8466677873
-- title:
--   The endpoint flow estimate $\hat g(j)$
-- statement:
--   Let $\pi$ be the intended distribution on the $m$ active ranks, $g$ a hidden vector on the chain with anchor value $g(x_0)=0$, and $(A,B)$ the queried pair. The **endpoint flow estimate** of $g(x_j)$ is
--   $$
--   \hat g(j)=\frac{\varphi_j(0,A)}{\pi(A)}\,g(x_A)+\mathbf 1\{A\ne B\}\,\frac{\varphi_j(A\wedge B,A\vee B)}{q(A\wedge B,A\vee B)}\bigl(g(x_{A\vee B})-g(x_{A\wedge B})\bigr),
--   $$
--   with $q(a,b)=2\Gamma(a,b)$, the probability that the pair of Algorithm 1 reveals the interval edge $(a,b)$. When $A=B$ the interval term is omitted.
--
--   It uses only the two observed values $g(x_A)$, $g(x_B)$ and the known distribution $\pi$; it is the estimator of Lemma 1 for the pair and flows of Section 3.3.
--
--   **Formalization Note** $g:\mathbb N\to\mathbb R$ on ranks; the anchor value $0$ is built in and only $g(A)$, $g(B)$ are read.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3.3, p.9; Algorithm 1 (Estimate), p.9

import Definitions.Def_OrderedExperts_phi
import Definitions.Def_OrderedExperts_gamma

namespace OrderedExperts

/-- **The endpoint flow estimate.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Algorithm 1 (Estimate), p.9, and
the display of Sec. 3.3, p.9: "Since `H(0, A) = g(xA)` and `q(0, A) = π(A)`, it reads
`ĝ(j) = φj(0, A)/π(A) · g(xA) + 1{A ≠ B} φj(A ∧ B, A ∨ B)/q(A ∧ B, A ∨ B) · (g(xA∨B) − g(xA∧B))`.
When `A = B`, the interval term is omitted", where for this pair "`q(0, a) = π(a)`,
`q(a, b) = π(a)κ(a, b) + π(b)κ(b, a) = 2Γ(a, b)`" (p.9).

`est m ξ π g A B j` is the estimate `ĝ(j)` of the hidden value `g(xj)` from the queried pair of ranks
`(A, B)` and the observed values `g(xA)`, `g(xB)`, with `q(A∧B, A∨B) = 2Γ(A∧B, A∨B)`.

**Formalization Note.** The hidden vector is `g : ℕ → ℝ` on ranks; the anchor value `g(x0) = 0` is
built in (the anchor increment is `g A`), and only `g A` and `g B` are read, so the estimate depends
on `g` only through the two observed values and on the law only through `π`. -/
noncomputable def est (m : ℕ) (ξ : ℝ) (π g : ℕ → ℝ) (A B j : ℕ) : ℝ :=
  phi π j 0 A / π A * g A +
    if A ≠ B then
      phi π j (min A B) (max A B) / (2 * gamma m ξ π A B) * (g (max A B) - g (min A B))
    else 0

end OrderedExperts


