-- Prove2me | Definitions.Def_LEDPCount_partialP
-- name    : LEDPCount_partialP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:18.073054+00:00
-- url     : https://prove2.me/theorems/e57165d4-663b-46de-b730-63d2ed55fcb7
-- title:
--   Partial derivative $\partial P(X)/\partial X_{i,j}$ of the counting polynomial, Eq. (5)
-- statement:
--   For a pattern $H$ and $i<j$, the partial derivative of the counting polynomial in the variable $X_{i,j}$ is
--   $$
--   \frac{\partial P(X)}{\partial X_{i,j}}=\frac{1}{|\mathrm{Aut}(H)|}\sum_{e\in E(H)}\ \sum_{\substack{\phi:V(H)\hookrightarrow[n]\\ \phi(e)=\{i,j\}}}\ \prod_{e'\in E(H)\setminus e}X_{\phi(e')}.
--   $$
--   It is the weight with which party $i$ corrects the linear part of the randomized-response error in the second round of LNC; it does not depend on $X_{i,j}$ itself.
--
--   **Formalization Note** The formula (5) is the definition, at the unordered pair $\{i,j\}$. A verification file proves that it is the derivative of $t\mapsto P(X[X_{\{i,j\}}:=t])$.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), §3, Eq. (5), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_LEDPCount_autCount

namespace LEDPCount

/-- The partial derivative `∂P(X)/∂X_{i,j}` of the counting polynomial, Eq. (5) (Chen–Peng,
arXiv:2611.05038, held version sha256 d18032b0…, §3, p.18, PDF p.20):
`∂P(X)/∂X_{i,j} = |Aut(H)|⁻¹ ∑_{e ∈ E(H)} ∑_{ϕ : V(H) ↪ [n], ϕ(e) = {i,j}} ∏_{e' ∈ E(H) \ e} X_{ϕ(e')}`.

**Formalization Note** The formula (5) is taken as the definition, at the unordered pair
`p = {i, j}`; it is the derivative of the multilinear polynomial (1) in the variable `X_p`. -/
noncomputable def partialP {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] {n : ℕ}
    (X : Sym2 (Fin n) → ℝ) (p : Sym2 (Fin n)) : ℝ :=
  (autCount H : ℝ)⁻¹ * ∑ e ∈ H.edgeFinset,
    ∑ ϕ ∈ (Finset.univ.filter fun ϕ : Fin k ↪ Fin n => e.map ϕ = p),
      ∏ e' ∈ H.edgeFinset.erase e, X (e'.map ϕ)

end LEDPCount


