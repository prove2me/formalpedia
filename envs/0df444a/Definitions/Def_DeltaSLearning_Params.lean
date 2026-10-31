-- Prove2me | Definitions.Def_DeltaSLearning_Params
-- name    : DeltaSLearning_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:41.026993+00:00
-- url     : https://prove2.me/theorems/b97ed4fb-ad26-4fcf-a90f-e3265fecfb29
-- title:
--   Cost, capacity and density parameters $(K,c,h,p,\beta,\rho)$
-- statement:
--   The parameters of the periodic-review, single-product, lost-sales inventory system with a fixed ordering cost: a fixed cost $K>0$ per order, a unit ordering cost $c\ge 0$, a unit holding cost $h>0$, a unit lost-sales penalty $p>c$, a warehouse capacity $\beta\ge 0$ that caps the after-order inventory level, and a constant $\rho>0$ bounding the density of the demand (Assumption 1(b)).
--
--   Every statement of the mission is about one such instance; bundling the ranges keeps the statements free of repeated side conditions.
--
--   **Formalization Note** The paper states $K>0$ (p.2), $\beta\ge0$ (p.7), $p>c$ (p.8) and $\rho>0$ (p.9). It does not state the signs of $c$ and $h$; we take $c\ge0$ and $h>0$, since they are per-unit costs, the paper divides by $h$ in (19), and with $c<0$ the bound $\gamma$ of (10) can be negative.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), §1 p.2, §2 p.7, §2.1 p.8, Assumption 1(b) p.9

import Mathlib

namespace DeltaSLearning

/-- The parameters of the periodic-review lost-sales inventory system with a fixed cost, with
their ranges: fixed ordering cost `K > 0`, unit ordering cost `c ≥ 0`, unit holding cost `h > 0`,
unit lost-sales penalty `p > c`, warehouse capacity `β ≥ 0`, and the density bound `ρ > 0` of
Assumption 1(b).
Yuan, Luo, Shi, *Marrying Stochastic Gradient Descent with Bandits: Learning Algorithms for
Inventory Systems with Fixed Costs*, SSRN 3329611 (accepted manuscript, Management Science 2021,
doi:10.1287/mnsc.2020.3799), §1 p.2 ("a constant K > 0"), §2 p.7 ("β ≥ 0"), §2.1 p.8
("p > c"), Assumption 1(b) p.9 ("ρ > 0").

**Formalization Note** The paper calls `c` and `h` per-unit costs without stating a sign. We take
`c ≥ 0` and `h > 0`: the paper divides by `h` in (19), and with `c < 0` the bound `γ` of (10) can
be negative, so Lemma 1 would fail. -/
structure Params where
  K : ℝ
  c : ℝ
  h : ℝ
  p : ℝ
  β : ℝ
  ρ : ℝ
  K_pos : 0 < K
  c_nonneg : 0 ≤ c
  h_pos : 0 < h
  c_lt_p : c < p
  β_nonneg : 0 ≤ β
  ρ_pos : 0 < ρ

end DeltaSLearning


