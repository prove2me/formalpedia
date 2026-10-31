-- Prove2me | Definitions.Def_PCLAssort_LPzFeasible
-- name    : PCLAssort_LPzFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:17.875731+00:00
-- url     : https://prove2.me/theorems/215ddec0-202d-41f0-a37b-9956c20b8255
-- title:
--   Feasible set of LP$(z)$
-- statement:
--   For sizes $s_i$ and a capacity $c$ (the knapsack family of §4), the feasible set of LP$(z)$ on the graph $G_z$ is the set of $(x,y)$ with
--
--   1. $y_{ij}\le x_i$ and $y_{ij}\le 1-x_j$ for $(i,j)\in E$;
--   2. $x_i\le 1$ for $i\in[n]$;
--   3. $\sum_{i\in[n]}s_ix_i\le c$;
--   4. $x_{n+1}=0$;
--   5. $x,y\ge 0$.
--
--   It is the relaxation of IP$_2(z)$; only the objective depends on $z$.
--
--   **Formalization Note** Vertices are `Option (Fin n)`; $y$ is fixed to $0$ off $E$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.1, LP$(z)$, p.792 (PDF p.8)

import Mathlib
import Definitions.Def_PCLAssort_pclEdges

namespace PCLAssort

/-- Feasible set of LP(z) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.1, p.792), for the knapsack family
`𝓕 = {x ∈ {0,1}^n | ∑_i s_i x_i ≤ c}` of §4: `y_ij ≤ x_i`, `y_ij ≤ 1 − x_j` for `(i,j) ∈ E`;
`x_i ≤ 1` for `i ∈ [n]`; `∑_{i∈[n]} s_i x_i ≤ c`; `x_{n+1} = 0`; `x, y ≥ 0`.

**Formalization Note.** Vertices are `Option (Fin n)` (`none` = dummy), `E` is `pclEdges n`, and
`y` is pinned to `0` off `E`. The feasible set does not depend on `z`; only the objective does. -/
def LPzFeasible (n : ℕ) (s : Fin n → ℝ) (c : ℝ) :
    Set ((Option (Fin n) → ℝ) × (Option (Fin n) × Option (Fin n) → ℝ)) :=
  {p | (∀ e ∈ pclEdges n, p.2 e ≤ p.1 e.1) ∧ (∀ e ∈ pclEdges n, p.2 e ≤ 1 - p.1 e.2) ∧
    (∀ i : Fin n, p.1 (some i) ≤ 1) ∧ ∑ i : Fin n, s i * p.1 (some i) ≤ c ∧ p.1 none = 0 ∧
    (∀ u, 0 ≤ p.1 u) ∧ (∀ e ∈ pclEdges n, 0 ≤ p.2 e) ∧ (∀ e, e ∉ pclEdges n → p.2 e = 0)}

end PCLAssort


