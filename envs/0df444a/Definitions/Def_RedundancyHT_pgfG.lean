-- Prove2me | Definitions.Def_RedundancyHT_pgfG
-- name    : RedundancyHT_pgfG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:33.89632+00:00
-- url     : https://prove2.me/theorems/34d3af88-8925-40b0-b99a-14aa28ed558c
-- title:
--   The function $g(z)$ of Proposition 2
-- statement:
--   For $z\in\mathbb C^n$,
--   $$g(z)=\sum_{L=0}^{N}\sum_{u\in\mathcal N_L}\prod_{l=1}^{L}\frac{\mu_{u_l}}{\lambda_{\mathcal C(u_1,\dots,u_l)}}\sum_{m=0}^{|\mathcal S|}\sum_{S\in\mathcal S_m^{u}}\prod_{j=1}^{m}\frac{N\lambda p_{S_j}z_{S_j}}{\mu(S_1,\dots,S_j)}\Bigl(1-\frac{N\lambda}{\mu(S_1,\dots,S_j)}\sum_{i=1}^{j}p_{S_i}z_{S_i}\Bigr)^{-1},$$
--   where $\mathcal N_L$ is the set of ordered vectors of $L$ distinct servers and $\mathcal S_m^{u}$ the set of ordered vectors of $m$ distinct job types with no compatible server in $u$.
--
--   **Formalization Note** The product over $j$ covers both factors. The vectors $u$ consist of useful servers, which is the printed set when every server is useful. A server compatible with no job type would otherwise give a zero denominator.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Proposition 2, p.33

import Definitions.Def_RedundancyHT_pgfSum
import Definitions.Def_RedundancyHT_lamC
import Definitions.Def_RedundancyHT_useful

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay Classical
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The function `g(z)` of Proposition 2** (arXiv:2005.14566v5, p.33):
`Σ_{L=0}^{N} Σ_{u∈𝒩_L} ∏_{l=1}^{L} µ_{u_l}/λ_{𝒞(u₁,…,u_l)} Σ_{m} Σ_{S∈𝒮_m^u} ∏_{j} …`.

**Formalization Note.**
1. The page prints one product over `j` and sets the parenthesis inside it. It covers both factors,
   as in (10) and in the three steps of the proof of Proposition 1 that the proof of Proposition 2
   invokes (p.34).
2. `u` runs over ordered vectors of distinct **useful** servers, in order of longest idleness. If
   every server is useful this is the printed set `𝒩_L`. Otherwise a printed term can divide by
   `λ_𝒞 = 0`, while a server compatible with no type has no effect on the system.
3. The inner sum runs over the types with no compatible server in `u`, the complement of
   `someClasses D.edge u`. -/
def pgfG {n m : ℕ} (D : Model n m) (lam : ℝ) (z : Fin n → ℂ) : ℂ :=
  ∑ L ∈ Finset.range (m + 1),
    ∑ u ∈ (Finset.univ : Finset (Fin L ↪ Fin m)).filter (fun u => ∀ l, useful D (u l)),
      ((∏ l, D.service (u l) / lamC D lam (prefixSet u l) : ℝ) : ℂ) *
        pgfSum D lam (someClasses D.edge (Finset.univ.image u))ᶜ z

end RedundancyHT


