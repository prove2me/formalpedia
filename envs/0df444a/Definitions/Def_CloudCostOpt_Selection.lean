-- Prove2me | Definitions.Def_CloudCostOpt_Selection
-- name    : CloudCostOpt_Selection
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:04:42.199478+00:00
-- url     : https://prove2.me/theorems/ef2b3d3d-6d7c-4c4f-9ff7-2dcb95855c18
-- title:
--   A selection of optimal resources $j^*(i,s,l)$
-- statement:
--   A **selection of optimal resources** consists of
--
--   1. for every order type $i$, a late resource $j_i^{Late,*}$ with $\beta_{i,j_i^{Late,*}}>0$ that minimizes $(R_j+W_i)/\beta_{i,j}$ over $\{j:\beta_{i,j}>0\}$;
--   2. for every $i$, $s<\delta_i$ and $l\le L_i-1$, a resource $j^{Early}(i,s,l)$ that minimizes $R_j+\beta_{i,j}f_i(s+1,l+1)+\tilde\beta_{i,j}f_i(s+1,l)$ over all $j$, including the dummy resource.
--
--   The paper writes "the" argmin; ties are allowed here, and every theorem of the mission holds for every selection. A selection depends on $R,W,\beta,\delta,L$ only, not on the arrival rates.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, Lemma 1, p.12; §3, p.13 (j*(i, s, l) = argmin_j …)

import Mathlib
import Definitions.Def_CloudCostOpt_fDP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **A selection of optimal resources `j*(i, s, l)`** (Lemma 1, p.13): one late resource
`j^{Late,*}_i`, a minimizer of `(R_j + Wᵢ)/β_{i,j}` over `{j | β_{i,j} > 0}`, used in every late
period; and, for every `s < δᵢ` and `l < Lᵢ`, a minimizer `jEarly i s l` of
`R_j + β_{i,j} fᵢ(s + 1, l + 1) + β̃_{i,j} fᵢ(s + 1, l)` over all `j` (including the dummy `0`).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, Lemma 1, p.12, and §3, p.13 ("`j*(i, s, l) = argmin_j …`").

Formalization Note: the paper writes "the" argmin; ties are allowed here and every theorem of the
mission holds for every selection.  The selection depends on `R, W, β, δ, L` only, not on the
arrival rates. -/
structure Selection (S : System) where
  /-- `j^{Late,*}_i` -/
  jLate : Fin S.I → Fin (S.J + 1)
  jLate_pos : ∀ i, 0 < S.β i (jLate i)
  jLate_min : ∀ i j, 0 < S.β i j →
    (resCost S (jLate i) + S.W i) / S.β i (jLate i) ≤ (resCost S j + S.W i) / S.β i j
  /-- `j*(i, s, l)` before the deadline -/
  jEarly : Fin S.I → ℕ → ℕ → Fin (S.J + 1)
  jEarly_min : ∀ i s l (j : Fin (S.J + 1)), s < S.δ i → l < S.L i →
    resCost S (jEarly i s l) + S.β i (jEarly i s l) * fDP S i (s + 1) (l + 1) +
        (1 - S.β i (jEarly i s l)) * fDP S i (s + 1) l ≤
      resCost S j + S.β i j * fDP S i (s + 1) (l + 1) + (1 - S.β i j) * fDP S i (s + 1) l

end CloudCostOpt


