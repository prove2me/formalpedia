-- Prove2me | Definitions.Def_ROLDescent_LinkGapGE
-- name    : ROLDescent_LinkGapGE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:22.424372+00:00
-- url     : https://prove2.me/theorems/85b58929-3492-4c73-a71c-28f4c5820c1a
-- title:
--   Link-walk spectral gap $\mathrm{gap}(\mathrm{id}-P_\tau)\ge\lambda$
-- statement:
--   For a face $\tau$ and a real number $\lambda$, the link walk has **spectral gap at least $\lambda$** if
--
--   $$\mathrm{gap}(\mathrm{id} - P_\tau) = 1 - \beta_2(P_\tau) \ge \lambda \quad \text{in } L^2(\pi_\tau),$$
--
--   where $\beta_2(P_\tau)$ is the second-largest eigenvalue of $P_\tau$ (not the absolute spectral gap; bipartite links are allowed). Equivalently, for every real function $g$ on $N_\tau$ with $\sum_{i} \deg(i)\, g(i) = 0$, where $\deg(i) = (m_\tau - 1) W_{\tau i}$,
--
--   $$\sum_{i,j \in N_\tau} W_{\tau ij}\, g(i)\, g(j) \le (1 - \lambda) \sum_{i \in N_\tau} \deg(i)\, g(i)^2 .$$
--
--   **Formalization Note** Stated through the public `HDXConc.SecondEigLE` on the link vertices $N_\tau$ (public `HDXConc.linkVerts`) with the public link edge weights `HDXConc.linkWeight` ($W_{\tau ij}$ for distinct $i, j \notin \tau$, zero on the diagonal) and threshold $1-\lambda$. The degree measure is proportional to $\pi_\tau$ and the walk of the weights is $P_\tau$, which is self-adjoint in $L^2(\pi_\tau)$; by Courant–Fischer the Rayleigh form is the eigenvalue bound, and real test functions suffice.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.1, eq. (72), p.30 (PDF 30)

import Mathlib
import Definitions.Def_HDXConc_SecondEigLE
import Definitions.Def_HDXConc_linkWeight

namespace ROLDescent

/-- **Link-walk spectral gap at least λ.** Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.1, eq. (72), p.30 (PDF 30):
"let λ_τ ∈ (0, 2] be a specified lower bound on the spectral gap of the classical link walk P_τ,
measured by its normalized Laplacian id − P_τ: gap(id − P_τ) = 1 − β₂(P_τ) ≥ λ_τ > 0 in L²(π_τ).
Here β₂(P_τ) denotes the second-largest eigenvalue."

**Formalization Note** Stated as `β₂ ≤ 1 − λ` through the public `HDXConc.SecondEigLE` on the link
vertices `N_τ` (public `HDXConc.linkVerts`) with the public link edge weights `HDXConc.linkWeight`,
which equal `W_τij` for distinct `i, j ∉ τ` and `0` on the diagonal. On `N_τ` their degrees are
`(m_τ − 1) W_τi`, so the walk of `SecondEigLE` is exactly `P_τ` and its degree measure is
proportional to `π_τ`. `P_τ` is self-adjoint in L²(π_τ), so by Courant–Fischer (with at least two
states) "β₂(P_τ) ≤ 1 − λ" is the Rayleigh bound on degree-mean-zero test functions. Real test
functions suffice because `P_τ` is a real operator self-adjoint in L²(π_τ). -/
def LinkGapGE {V : Type*} [Fintype V] [DecidableEq V] (X : Finset (Finset V)) (d : ℕ)
    (w : Finset V → ℝ) (τ : Finset V) (lam : ℝ) : Prop :=
  HDXConc.SecondEigLE (HDXConc.linkVerts X τ) (HDXConc.linkWeight X d w τ) (1 - lam)

end ROLDescent


