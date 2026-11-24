-- Prove2me | Definitions.Def_BB6Theta
-- name    : BB6Theta
-- status  : Definition
-- author  : @alon yuval
-- created : 2026-11-24T06:57:26.493185+00:00
-- url     : https://prove2.me/theorems/a8555ad9-a533-4c37-87d5-3410ea579db4
-- title:
--   The combinatorial quantity $\Theta(K_0,I)$ of the Mignotte–Voutier kit (eq. (3.1))
-- statement:
--   For non-negative integers $K_0$ and $I$, `BB6Theta.theta K0 I` is the quantity of eq. (3.1) of the Mignotte–Voutier kit (arXiv:2205.08899): $$\Theta(K_0,I)=\min\Bigl\{\sum_{(k,m)\in P}(k+m)\;:\;P\subseteq\mathbb N^2,\ |P|=I,\ m\le K_0\text{ for all }(k,m)\in P\Bigr\}.$$ It is the least total degree of $I$ distinct monomials $w^k z^m$ with $z$-degree at most $K_0$. It is the vanishing order that Lemma 3.6 (from Waldschmidt's Lemma 7.2) guarantees for the auxiliary determinants $\Psi_{\mathcal I}$ at $x=0$. The set is never empty, so the minimum (`sInf` on $\mathbb N$) exists.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Section 3.2, eq. (3.1).

import Mathlib

namespace BB6Theta

/-- `Θ(K₀, I)` of eq. (3.1) of the Mignotte–Voutier kit: the least value of `Σ (k + m)` over sets of
`I` distinct pairs `(k, m) ∈ ℕ²` with `m ≤ K₀`. -/
noncomputable def theta (K0 I : ℕ) : ℕ :=
  sInf {s : ℕ | ∃ P : Finset (ℕ × ℕ), P.card = I ∧ (∀ p ∈ P, p.2 ≤ K0) ∧ s = ∑ p ∈ P, (p.1 + p.2)}

end BB6Theta


