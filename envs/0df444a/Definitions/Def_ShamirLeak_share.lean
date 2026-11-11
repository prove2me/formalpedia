-- Prove2me | Definitions.Def_ShamirLeak_share
-- name    : ShamirLeak_share
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:51.375597+00:00
-- url     : https://prove2.me/theorems/5c40b19d-af0e-4b34-b3d0-76f98d1f261d
-- title:
--   The Shamir sharing law $\mathrm{share}_\alpha(s)$ (Definition 3)
-- statement:
--   Let $\alpha=(\alpha_1,\dots,\alpha_n)$ be evaluation points and $k\ge1$ a threshold. To share a secret $s\in\mathbb F_p$, the $(n,k,\alpha)$-**Shamir scheme** samples $Z_1,\dots,Z_{k-1}$ independent and uniform in $\mathbb F_p$, forms
--
--   $$P(X)=s+\sum_{j=1}^{k-1}Z_jX^j,$$
--
--   and gives party $i$ the share $P(\alpha_i)$. The distribution of the share vector $(P(\alpha_1),\dots,P(\alpha_n))$ is denoted $\mathrm{share}_\alpha(s)$. In the paper the evaluation points are distinct and nonzero.
--
--   This is the object of the goal theorem: leakage resilience compares the leakage of $\mathrm{share}_\alpha(s)$ and $\mathrm{share}_\alpha(s')$.
--
--   **Formalization Note** The law is the push-forward of the uniform distribution on coefficient vectors `Fin (k - 1) → ZMod p`; the coefficient with index $j$ is the paper's $Z_{j+1}$ and multiplies $X^{j+1}$. The reconstruction clause of Definition 3 is not part of the law. For $k=1$ every share equals $s$.
-- source:
--   Nguyen, Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate, arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 3, p.11 (PDF 13)

import Mathlib

namespace ShamirLeak

/-- The **Shamir sharing law** `share_α(s)` of the `(n, k, α)`-Shamir scheme
(Definition 3, p.11 (PDF p.13)): sample `Z₁, …, Z_{k−1}` independent and uniform in `𝔽_p`, form
`P(X) = s + ∑_{j=1}^{k−1} Z_j X^j`, and give party `i` the share `P(αᵢ)`.
H. H. Nguyen, *Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate*,
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 3, p.11 (PDF p.13).

**Formalization Note.** The coefficient vector `(Z₁, …, Z_{k−1})` is a uniform element of
`Fin (k − 1) → ZMod p`; the coefficient with index `j : Fin (k − 1)` is the paper's `Z_{j+1}` and
multiplies `X^{j+1}` (never `X^j`, which would add a second constant term). The law is the
push-forward of that uniform law. The paper's standing conditions on `α` (distinct, nonzero
coordinates) are hypotheses of the statements, not part of the definition. For `k = 1` there are
no random coefficients and every share equals `s`. -/
noncomputable def share {p n : ℕ} [NeZero p] (α : Fin n → ZMod p) (k : ℕ) (s : ZMod p) :
    PMF (Fin n → ZMod p) :=
  (PMF.uniformOfFintype (Fin (k - 1) → ZMod p)).map
    (fun Z i => s + ∑ j : Fin (k - 1), Z j * α i ^ (j.val + 1))

end ShamirLeak


