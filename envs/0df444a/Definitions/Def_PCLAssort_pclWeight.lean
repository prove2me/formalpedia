-- Prove2me | Definitions.Def_PCLAssort_pclWeight
-- name    : PCLAssort_pclWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:29.067754+00:00
-- url     : https://prove2.me/theorems/c0ed661b-16cf-4534-8d16-947cc7386ea5
-- title:
--   Edge weights $w_{ij}(z)$ of the reduction graph
-- statement:
--   For a nest $(i,j)$ let $a=v_i^{1/\gamma_{ij}}$, $b=v_j^{1/\gamma_{ij}}$, $D=(a+b)^{1-\gamma_{ij}}$ and $\bar r_i=r_i-z$. The pair $(i,j)$ puts
--
--   1. $\bar r_i a/D$ on the edge $(i,n+1)$ and $\bar r_j b/D$ on $(j,n+1)$;
--   2. $v_i\bar r_i-\bar r_i a/D$ on the edge $(i,j)$ and $v_j\bar r_j-\bar r_j b/D$ on $(j,i)$.
--
--   The weight $w_e(z)$ of an edge is the sum of what all ordered pairs put on it: $w_{i,n+1}(z)=\sum_{k\ne i}\xi_{ik}$ and $w_{ij}(z)=\psi_{ij}$ for products $i\neq j$, as in (6). The weights are affine in $z$, and the cut of an assortment equals $h_z$ (Lemma 1).
--
--   **Formalization Note** The subscripts of $\xi^-$ and $\psi^-$ in (4)–(5) are inconsistent with the prose on pp.790–791; the closed forms above are used. Pairs that are not edges get weight $0$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), equations (4)–(6), pp.790–791 (PDF pp.6–7)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_xiShare

namespace PCLAssort

/-- The edge weights `w_ij(z)` of the reduction graph `G_z`, equations (4)–(6) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, pp.790–791).
The ordered pair `(i, j)`, with `a = v_i^{1/γ_ij}`, `b = v_j^{1/γ_ij}`, `D = (a + b)^{1−γ_ij}`, puts
`r̄_i a/D` on `(i, n+1)`, `r̄_j b/D` on `(j, n+1)`, `v_i r̄_i − r̄_i a/D` on `(i, j)` and
`v_j r̄_j − r̄_j b/D` on `(j, i)`; the final weight of an edge is the sum over all ordered pairs:
`w_{i,n+1}(z) = ∑_{k ∈ [n]∖{i}} ξ_ik` and `w_ij(z) = ψ_ij` for `i, j ∈ [n]`.

**Formalization Note.** The subscripts of `ξ⁻` and `ψ⁻` in (4)–(5) are inconsistent with the prose
of p.790–791; the closed forms above are used, so that `ξ_ik` is what the pairs `(i, k)` and
`(k, i)` put on `(i, n+1)`, and `ψ_ij` what the pairs `(i, j)` and `(j, i)` put on `(i, j)`.
Pairs that are not edges (`(n+1, ·)`, loops) get weight `0`. -/
noncomputable def pclWeight {n : ℕ} (I : PCLInstance n) (z : ℝ) :
    Option (Fin n) × Option (Fin n) → ℝ
  | (some i, none) => ∑ k ∈ Finset.univ.erase i, (xiShare I z i k i + xiShare I z k i i)
  | (some i, some j) =>
      if i = j then 0 else 2 * (I.v i * (I.r i - z)) - xiShare I z i j i - xiShare I z j i i
  | (none, _) => 0

end PCLAssort


