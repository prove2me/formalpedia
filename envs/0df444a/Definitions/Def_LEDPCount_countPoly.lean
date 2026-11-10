-- Prove2me | Definitions.Def_LEDPCount_countPoly
-- name    : LEDPCount_countPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:10.493802+00:00
-- url     : https://prove2.me/theorems/8eb9164c-818e-469a-a6bb-70cb56a3bf95
-- title:
--   Counting polynomial $P(X)$ of a pattern, Eq. (1)
-- statement:
--   Let $H$ be a pattern graph with $k$ vertices and let $X=(X_{i,j})_{i,j\in[n]}$ be a symmetric real matrix, with $X_e=X_{\min(i,j),\max(i,j)}$ for an unordered pair $e=\{i,j\}$. The **counting polynomial** of $H$ is
--   $$
--   P(X)=\frac{1}{|\mathrm{Aut}(H)|}\sum_{\phi:V(H)\hookrightarrow[n]}\ \prod_{e\in E(H)}X_{\phi(e)},
--   $$
--   where the sum ranges over all injections $\phi$ and $\phi(\{u,v\})=\{\phi(u),\phi(v)\}$. Evaluated at the adjacency matrix of a graph it counts the copies of $H$ (Eq. (1)); evaluated at a noisy estimate of the adjacency matrix it is the first term of the estimator LNC.
--
--   **Formalization Note** A symmetric matrix is a function on unordered pairs `Sym2 (Fin n)`, which is the paper's upper-triangular convention; vertices are $0,\dots,n-1$. The diagonal is never read because $\phi$ is injective and $H$ has no loops.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), §1.2.1, Eq. (1), p.4 (PDF p.6); §2.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_LEDPCount_autCount

namespace LEDPCount

/-- The counting polynomial of a pattern `H` with `k` vertices, Eq. (1) (Chen–Peng,
arXiv:2611.05038, held version sha256 d18032b0…, §1.2.1, p.4, PDF p.6; also §2.1, p.14):
`P(X) = |Aut(H)|⁻¹ ∑_{ϕ : V(H) ↪ [n]} ∏_{e ∈ E(H)} X_{ϕ(e)}`, the sum over all injections
`ϕ` and `ϕ(e) = {ϕ(u), ϕ(v)}` for `e = {u, v}`.

**Formalization Note** A symmetric matrix `X = (X_{i,j})` is a function on unordered pairs
`Sym2 (Fin n)`; this is the paper's convention `X_e = X_{min(i,j), max(i,j)}` (p.14). Vertices
are `Fin n` (0-based). The diagonal is never read, since `ϕ` is injective and `H` is loopless. -/
noncomputable def countPoly {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] {n : ℕ}
    (X : Sym2 (Fin n) → ℝ) : ℝ :=
  (autCount H : ℝ)⁻¹ * ∑ ϕ : Fin k ↪ Fin n, ∏ e ∈ H.edgeFinset, X (e.map ϕ)

end LEDPCount


