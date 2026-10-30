-- Prove2me | Definitions.Def_NestedLogitNBR_factor6Term
-- name    : NestedLogitNBR_factor6Term
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:39:13.845882+00:00
-- url     : https://prove2.me/theorems/9b6893b7-f4e3-4eb8-a9e6-f4a5183856c8
-- title:
--   Term of the performance factor (6) for nest $i$ and index $j$
-- statement:
--   With $R_i$, $V_i$ and $N_{ij}$ as in the nested logit model with $v_{i0}=0$, the expression in curly brackets of the performance factor (6) (p. 19) is, for nest $i$ and $j=2,\dots,n$,
--
--   $$
--   \frac{R_i(N_{i,j-1})}{R_i(N_{ij})}\ \wedge\ \frac{R_i(N_{ij})}{R_i(N_{i,j-1})}\cdot\frac{V_i(N_{ij})^{\gamma_i}}{V_i(N_{i,j-1})^{\gamma_i}},\qquad a\wedge b=\min\{a,b\}.
--   $$
--
--   The first term measures how much the average revenue drops when product $j$ is added, the second how much the nest's revenue contribution grows.
--
--   **Formalization Note** The powers are real powers of nonnegative bases. When a denominator vanishes (a prefix of zero-revenue or zero-weight products, which the model allows) the paper's term is undefined; Lean's $x/0=0$ then gives a value at most $0$, which the factor `factor6` overrides by taking the maximum with $1$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), eq. (6), p. 19 (expression in curly brackets)

import Mathlib
import Definitions.Def_NestedLogitNBR_nbr
import Definitions.Def_NestedLogitNBR_prefWeight
import Definitions.Def_NestedLogitNBR_nestRevenue

namespace NestedLogitNBR

/-- **The term in curly brackets of the performance factor (6), for nest `i` and index `j`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), eq. (6), p. 19:
`max_{i∈M, j=2,…,n} { R_i(N_{i,j−1})/R_i(N_ij) ∧ (R_i(N_ij)/R_i(N_{i,j−1})) (V_i(N_ij)^{γ_i} /
V_i(N_{i,j−1})^{γ_i}) }`, "where we let `a ∧ b = min{a, b}`".

`factor6Term r v γ i j = min (R_i(N_{i,j−1}) / R_i(N_ij))
((R_i(N_ij) / R_i(N_{i,j−1})) · (V_i(N_ij)^{γ_i} / V_i(N_{i,j−1})^{γ_i}))`, for the paper's
index `j` (a natural number, used for `j = 2, …, n`).

**Formalization Note.** The powers are `Real.rpow` of nonnegative bases. The paper leaves the
term undefined when a denominator vanishes (a zero-revenue or zero-weight prefix, which its model
allows, p. 7); there Lean's `x / 0 = 0` gives a value `≤ 0`, and the factor `factor6` takes
the maximum with `1`. `j - 1` is natural-number subtraction, exact for `j ≥ 2`. -/
noncomputable def factor6Term {m n : ℕ} (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (i : Fin m)
    (j : ℕ) : ℝ :=
  min (nestRevenue r v i (nbr (j - 1)) / nestRevenue r v i (nbr j))
    (nestRevenue r v i (nbr j) / nestRevenue r v i (nbr (j - 1)) *
      (prefWeight v i (nbr j) ^ γ i / prefWeight v i (nbr (j - 1)) ^ γ i))

end NestedLogitNBR


