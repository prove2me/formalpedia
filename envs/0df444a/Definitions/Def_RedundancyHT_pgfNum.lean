-- Prove2me | Definitions.Def_RedundancyHT_pgfNum
-- name    : RedundancyHT_pgfNum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:26.043982+00:00
-- url     : https://prove2.me/theorems/e96ae298-9d5d-433f-a99c-c065ea6cb4e9
-- title:
--   The factor $N\lambda p_{S_j}z_{S_j}/\mu(S_1,\dots,S_j)$ of (10)
-- statement:
--   The first factor in (10): for an ordered vector $S$ of distinct job types and $z\in\mathbb C^{n}$,
--   $$\frac{N\lambda p_{S_j}z_{S_j}}{\mu(S_1,\dots,S_j)}.$$
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Proposition 1, display (10), p.13

import Definitions.Def_RedundancyHT_muPrefix
import Definitions.Def_RedundancyHT_pOf

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The factor `N λ p_{S_j} z_{S_j} / µ(S₁,…,S_j)` of (10)** (arXiv:2005.14566v5, p.13). -/
def pgfNum {n m k : ℕ} (D : Model n m) (lam : ℝ) (S : Fin k ↪ Fin n) (z : Fin n → ℂ) (j : Fin k) :
    ℂ :=
  ((m : ℝ) * lam * pOf D (S j) : ℝ) * z (S j) / (muPrefix D S j : ℝ)

end RedundancyHT


