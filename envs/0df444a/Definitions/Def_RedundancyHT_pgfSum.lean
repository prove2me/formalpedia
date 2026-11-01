-- Prove2me | Definitions.Def_RedundancyHT_pgfSum
-- name    : RedundancyHT_pgfSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:37.971415+00:00
-- url     : https://prove2.me/theorems/2f41c2a2-c82a-4221-83d1-eb2d8d34de03
-- title:
--   The sum $f(z)$ of (10), over ordered vectors of distinct job types from a set
-- statement:
--   For a set $A$ of job types and $z\in\mathbb C^n$,
--   $$\sum_{k=0}^{|\mathcal S|}\ \sum_{\substack{[S_1,\dots,S_k]\\ S_j\in A,\ \text{distinct}}}\ \prod_{j=1}^{k}\frac{N\lambda p_{S_j}z_{S_j}}{\mu(S_1,\dots,S_j)}\ \prod_{j=1}^{k}\Bigl(1-\frac{N\lambda}{\mu(S_1,\dots,S_j)}\sum_{i=1}^{j}p_{S_i}z_{S_i}\Bigr)^{-1}.$$
--   With $A=\mathcal S$ this is the function $f$ of (10): the term $k=0$ is the empty vector and gives the leading $1$. With $A$ the job types having no compatible server in $u$, it is the inner sum of Proposition 2.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Proposition 1, display (10), p.13, Proposition 2, p.33, and display (43), p.34

import Definitions.Def_RedundancyHT_pgfNum
import Definitions.Def_RedundancyHT_pgfDen

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The sum of (10) over ordered vectors of distinct types from `A`**
(arXiv:2005.14566v5, Proposition 1, p.13, Proposition 2, p.33, and (43), p.34):
`Σ_{k=0}^{|𝒮|} Σ_{S} ∏_{j} N λ p_{S_j} z_{S_j} / µ(S₁,…,S_j) ∏_{j} (1 − …)^{-1}`, over injections
`S : Fin k ↪ Fin n` with values in `A`.

**Formalization Note.** `k = 0` is the single empty vector, with empty products, so its term is the
leading `1` of (10). Thus `f(z) = pgfSum D lam Finset.univ z`, and for `A` the types not compatible
with `u`, this is the inner sum of Proposition 2. -/
def pgfSum {n m : ℕ} (D : Model n m) (lam : ℝ) (A : Finset (Fin n)) (z : Fin n → ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    ∑ S ∈ (Finset.univ : Finset (Fin k ↪ Fin n)).filter (fun S => ∀ j, S j ∈ A),
      (∏ j, pgfNum D lam S z j) * ∏ j, (pgfDen D lam S z j)⁻¹

end RedundancyHT


