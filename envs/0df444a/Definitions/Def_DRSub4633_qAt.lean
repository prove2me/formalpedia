-- Prove2me | Definitions.Def_DRSub4633_qAt
-- name    : DRSub4633_qAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:22.420234+00:00
-- url     : https://prove2.me/theorems/0dcca5ae-667b-4a8e-be07-439bca54dc7c
-- title:
--   The weight $q_i$ of the large label $i$
-- statement:
--   For the state $x$ and a label $i\in\{1,\dots,m\}$ of the large order, $q_i$ is the weight of the coordinate with that label: $q_1=1$ (the dummy coordinate), and for $i\ge 2$, $q_i=\max\{x_j,1-x_j\}$ for the original large coordinate $j$ with label $i$. The weights are nonincreasing in $i$.
--
--   **Formalization Note** For $i\ge 2$ the value is written as a sum of $q_j$ over the coordinates with label $i$, which has exactly one term when $2\le i\le m$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eqs. (12) and (16), pp.10–11

import Mathlib
import Definitions.Def_DRSub4633_sPar
import Definitions.Def_DRSub4633_qLarge
import Definitions.Def_DRSub4633_largePos

namespace DRSub4633

/-- **The weight `qᵢ` of the large coordinate with label `i`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1,
Eqs. (12) and (16), pp.10–11. Label `1` is the dummy coordinate, with `q₁ = 1` (p.10: "its weight in
(12) is `q = 1`"); a label `i ≥ 2` carries the original large coordinate `j` with `largePos x j = i`
and `qᵢ = max{x_j, 1 − x_j}`.

**Formalization Note.** For `i ≥ 2` the value is the sum of `q_j` over the large coordinates with
label `i`; there is exactly one such coordinate for `2 ≤ i ≤ m` (labels are distinct), so the sum is
its weight. For `i > m` the sum is empty (`0`); such labels are not used. -/
noncomputable def qAt {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : ℕ) : ℝ :=
  if i ≤ 1 then 1
  else ∑ j ∈ Finset.univ.filter (fun j : Fin n => sPar < x j ∧ largePos x j = i), qLarge x j

end DRSub4633


