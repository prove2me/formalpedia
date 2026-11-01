-- Prove2me | Definitions.Def_RedundancyHT_pgfDen
-- name    : RedundancyHT_pgfDen
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:50.535719+00:00
-- url     : https://prove2.me/theorems/3cff35cc-1ce7-42ed-997b-6955d5da6f6e
-- title:
--   The factor $1-\frac{N\lambda}{\mu(S_1,\dots,S_j)}\sum_{i\le j}p_{S_i}z_{S_i}$ of (10)
-- statement:
--   The quantity whose inverse is the second factor in (10): for an ordered vector $S$ of distinct job types and $z\in\mathbb C^{n}$,
--   $$1-\frac{N\lambda}{\mu(S_1,\dots,S_j)}\sum_{i=1}^{j}p_{S_i}z_{S_i}.$$
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Proposition 1, display (10), p.13

import Definitions.Def_RedundancyHT_muPrefix
import Definitions.Def_RedundancyHT_pOf

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The factor `1 − (N λ / µ(S₁,…,S_j)) Σ_{i=1}^{j} p_{S_i} z_{S_i}` of (10)**, before inversion
(arXiv:2005.14566v5, p.13). -/
def pgfDen {n m k : ℕ} (D : Model n m) (lam : ℝ) (S : Fin k ↪ Fin n) (z : Fin n → ℂ) (j : Fin k) :
    ℂ :=
  1 - (((m : ℝ) * lam / muPrefix D S j : ℝ) : ℂ) *
    ∑ i ∈ Finset.univ.filter (fun i => i ≤ j), (pOf D (S i) : ℂ) * z (S i)

end RedundancyHT


