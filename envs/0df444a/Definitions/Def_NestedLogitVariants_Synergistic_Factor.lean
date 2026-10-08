-- Prove2me | Definitions.Def_NestedLogitVariants_Synergistic_Factor
-- name    : NestedLogitVariants_Synergistic_Factor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:25:52.701625+00:00
-- url     : https://prove2.me/theorems/79b19c1d-c825-4e1d-9424-bca7b1b743fb
-- title:
--   (6), p. 19 — the terms of the performance factor α of the nested-by-revenue assortments
-- statement:
--   For a nest $i$ and an index $j \in \{2, \dots, n\}$, let $N_{ij} = \{1, \dots, j\}$ be the nested-by-revenue assortment of the $j$ highest-revenue products of nest $i$. The term of the factor (6) for $(i, j)$ is
--
--   $$\alpha_{ij} = \frac{R_i(N_{i,j-1})}{R_i(N_{ij})} \wedge \left(\frac{R_i(N_{ij})}{R_i(N_{i,j-1})}\, \frac{V_i(N_{ij})^{\gamma_i}}{V_i(N_{i,j-1})^{\gamma_i}}\right), \qquad a \wedge b = \min\{a, b\},$$
--
--   and the factor (6) of the paper is
--
--   $$\alpha = \max_{i \in M,\ j = 2, \dots, n} \alpha_{ij}.$$
--
--   This definition records the terms $\alpha_{ij}$ and the set $\{\alpha_{ij} : i \in M,\ 2 \le j \le n\}$; a statement about "the expression in (6)" takes a real number $\alpha$ together with the hypothesis that $\alpha$ is the greatest element of this set. The factor $\alpha$ is the performance guarantee of the nested-by-revenue assortments in §4.2.
--
--   **Formalization Note** Products are indexed from $0$ (`Fin n`), so $N_{ij}$ is `nbr n j`. The term is only used for $2 \le j \le n$, where the natural-number subtraction $j - 1$ does not truncate. Divisions are Lean's total division ($x/0 = 0$); every statement that uses the term assumes positive revenues, under which $R_i(N_{ij}) > 0$ and $V_i(N_{ij})^{\gamma_i} > 0$ for $j \ge 1$, so no denominator vanishes.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 19, display (6)

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Model

namespace NestedLogitVariants.Synergistic

variable {ι : Type*} {n : ℕ}

/-- The term of the performance factor (6) (p. 19) for nest `i` and index `j`:
`R_i(N_{i,j−1}) / R_i(N_{ij}) ∧ (R_i(N_{ij}) / R_i(N_{i,j−1})) (V_i(N_{ij})^{γ_i} / V_i(N_{i,j−1})^{γ_i})`,
where `a ∧ b = min {a, b}`. The factor (6) is the maximum of these terms over `i ∈ M` and
`j = 2, …, n`; the term is only used with `2 ≤ j ≤ n`, so the natural-number subtraction `j - 1`
never truncates. -/
noncomputable def alphaTerm (I : Instance ι n) (i : ι) (j : ℕ) : ℝ :=
  min (R I i (nbr n (j - 1)) / R I i (nbr n j))
    (R I i (nbr n j) / R I i (nbr n (j - 1)) *
      (nestWeight I i (nbr n j) / nestWeight I i (nbr n (j - 1))))

/-- The set of the terms of (6): `{alphaTerm I i j : i ∈ M, j = 2, …, n}`. The factor `α` of (6) is
its greatest element (`IsGreatest (alphaTerms I) α`). -/
def alphaTerms (I : Instance ι n) : Set ℝ :=
  {a | ∃ i, ∃ j ∈ Finset.Icc 2 n, a = alphaTerm I i j}

end NestedLogitVariants.Synergistic


