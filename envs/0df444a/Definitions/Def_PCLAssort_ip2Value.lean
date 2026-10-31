-- Prove2me | Definitions.Def_PCLAssort_ip2Value
-- name    : PCLAssort_ip2Value
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:20:38.805844+00:00
-- url     : https://prove2.me/theorems/ab3c8cea-9f08-4c8f-b9fd-d50a6235270e
-- title:
--   Optimal value of IP$_2(z)$
-- statement:
--   The integer program IP$_2(z)$ is
--
--   $$
--   \max\sum_{(i,j)\in E}w_{ij}(z)\,y_{ij}\quad\text{s.t.}\quad y_{ij}\le x_i,\ y_{ij}\le 1-x_j,\ y_{ij}\in\{0,1\}\ ((i,j)\in E),\ x_i\in\{0,1\}\ (i\in V),\ x_{n+1}=0,\ x\in\mathcal F.
--   $$
--
--   **Formalization Note** A binary $x$ with $x_{n+1}=0$ is an assortment $S\subseteq[n]$, and a binary $y$ is a set $Y\subseteq E$ of edges, each of which must leave $S$. The value is a supremum over this finite set of pairs $(S,Y)$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), IP$_2(z)$, p.791 (PDF p.7)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_pclEdges
import Definitions.Def_PCLAssort_pclWeight

namespace PCLAssort

/-- Optimal value of IP₂(z) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §3, p.791): maximize `∑_{(i,j)∈E} w_ij(z) y_ij` subject to
`y_ij ≤ x_i`, `y_ij ≤ 1 − x_j`, `y_ij ∈ {0,1}` for `(i,j) ∈ E`, `x_i ∈ {0,1}` for `i ∈ V`,
`x_{n+1} = 0`, `x ∈ 𝓕`.

**Formalization Note.** A binary `x` with `x_{n+1} = 0` is the image under `some` of an assortment
`S ⊆ [n]`, and `x ∈ 𝓕` means `S ∈ 𝓕`. A binary `y` is the set `Y ⊆ E` of edges with `y = 1`, and
the two constraints say that every edge of `Y` leaves the chosen vertex set. The supremum is over a
finite nonempty set (it contains `(∅, ∅)` when `∅ ∈ 𝓕`), hence attained. -/
noncomputable def ip2Value {n : ℕ} (I : PCLInstance n) (F : Set (Finset (Fin n))) (z : ℝ) : ℝ :=
  ⨆ q : {q : Finset (Fin n) × Finset (Option (Fin n) × Option (Fin n)) //
      q.1 ∈ F ∧ q.2 ⊆ pclEdges n ∧ ∀ e ∈ q.2, e.1 ∈ q.1.image some ∧ e.2 ∉ q.1.image some},
    ∑ e ∈ q.1.2, pclWeight I z e

end PCLAssort


