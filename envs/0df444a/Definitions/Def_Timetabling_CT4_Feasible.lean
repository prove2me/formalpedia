-- Prove2me | Definitions.Def_Timetabling_CT4_Feasible
-- name    : Timetabling_CT4_Feasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:32:29.118055+00:00
-- url     : https://prove2.me/theorems/4690ad63-315a-4296-9de0-a400e0ac306b
-- title:
--   Timetable of CT4: constraints (12)–(15)
-- statement:
--   Let $\bar x_{ijk} = 1$ if class $c_i$ and teacher $t_j$ meet at period $k$ for a lecture which is not a preassignment, and $\bar x_{ijk} = 0$ otherwise. A **timetable** of a CT4 instance is an array $\bar x$ satisfying
--
--   $$
--   \begin{aligned}
--   &\textstyle\sum_{k=1}^{p} \bar x_{ijk} = \bar r_{ij} && (i = 1,\dots,m;\ j = 1,\dots,n), && (12)\\
--   &\textstyle\sum_{j=1}^{n} \bar x_{ijk} \le \bar b_{ik} && (i = 1,\dots,m;\ k = 1,\dots,p), && (13)\\
--   &\textstyle\sum_{i=1}^{m} \bar x_{ijk} \le \bar c_{jk} && (j = 1,\dots,n;\ k = 1,\dots,p), && (14)\\
--   &\bar x_{ijk} = 0 \text{ or } 1 && (\text{all } i, j, k). && (15)
--   \end{aligned}
--   $$
--
--   Constraint (12) schedules every remaining lecture; (13) and (14) let a class or a teacher meet at most one lecture per period, and only when available; (15) makes the variables 0/1. Proposition 2.4 is about the existence of such an array.
--
--   **Formalization Note** Indices are 0-based and $\bar x$ is `Fin m → Fin n → Fin p → ℕ`.
-- source:
--   de Werra (1985), Sec. 2.2, p. 154, constraints CT4 (12)-(15). D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_Instance

namespace Timetabling.CT4

open Finset

/-- **A timetable of CT4: constraints (12)–(15).**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), Sec. 2.2, p. 154: "We define
x̄_ijk = 1 if class c_i and teacher t_j meet at period k for a lecture which is not a
preassignment and x̄_ijk = 0 otherwise. We have the following constraints CT4", (12)–(15).

`x i j k = x̄_ijk` is a timetable of the instance `I` when

* (12) `∑_k x̄_ijk = r̄_ij` for all `i`, `j`;
* (13) `∑_j x̄_ijk ≤ b̄_ik` for all `i`, `k`;
* (14) `∑_i x̄_ijk ≤ c̄_jk` for all `j`, `k`;
* (15) `x̄_ijk = 0` or `1` for all `i`, `j`, `k`.

**Formalization Note.** Indices are 0-based; the sums run over all of `Fin p`, `Fin n`, `Fin m`. -/
def Feasible {m n p : ℕ} (I : Instance m n p) (x : Fin m → Fin n → Fin p → ℕ) : Prop :=
  (∀ i j, ∑ k, x i j k = I.rbar i j) ∧
  (∀ i k, ∑ j, x i j k ≤ I.bbar i k) ∧
  (∀ j k, ∑ i, x i j k ≤ I.cbar j k) ∧
  (∀ i j k, x i j k = 0 ∨ x i j k = 1)

end Timetabling.CT4


