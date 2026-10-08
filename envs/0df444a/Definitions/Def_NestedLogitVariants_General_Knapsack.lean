-- Prove2me | Definitions.Def_NestedLogitVariants_General_Knapsack
-- name    : NestedLogitVariants_General_Knapsack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:26:56.623196+00:00
-- url     : https://prove2.me/theorems/9c114d47-b8e1-4839-9c31-160d529f54c1
-- title:
--   pp. 23–24 — the greedy solution ẑ_i(ε_i) of the continuous knapsack (11) and the assortment Ŝ_i(ε_i)
-- statement:
--   For a nest $i$ and a capacity $\epsilon_i\ge0$, the continuous knapsack problem (11) is
--   $$
--   \hat K_i(\epsilon_i)=\max\Big\{\sum_{j\in N}r_{ij}v_{ij}z_{ij} : \sum_{j\in N}v_{ij}z_{ij}\le\epsilon_i,\ 0\le z_{ij}\le\mathbf 1(v_{ij}\le\epsilon_i)\ \forall j\in N\Big\}.
--   $$
--   Since the utility-to-space ratio of product $j$ is $r_{ij}$, it is solved by the greedy rule: consider only the products whose preference weights do not exceed $\epsilon_i$, and fill the knapsack in order of decreasing revenue, taking each product fully while it fits and the next one fractionally. The resulting solution is $\hat z_i(\epsilon_i)$, and
--   $$
--   \hat S_i(\epsilon_i)=\{j\in N : \hat z_{ij}(\epsilon_i)=1\}
--   $$
--   is the set of products it takes fully (pp. 23–24).
--
--   In §5 the assortments $\hat S_i(\epsilon_i)$, $\epsilon_i\in[0,\infty]$, are the candidate assortments of nest $i$; §5 shows that each of them is one of the $N^k_{ij}$, which is how the collection of Theorem 11 arises.
--
--   **Formalization Note** $\hat z_i(\epsilon)$ is defined explicitly (`zhat`): for an eligible product $j$ ($v_{ij}\le\epsilon$), $\hat z_{ij}=\max\{0,\min\{1,(\epsilon-L_j)/v_{ij}\}\}$, where $L_j$ (`prefixLoad`) is the total weight of the eligible products with smaller index; ineligible products get $0$. Ties in revenue are broken by index. The page's $\epsilon_i=\infty$ adds nothing, since for $\epsilon\ge\sum_jv_{ij}$ the greedy rule already takes every product.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 23–24, problem (11) and the definitions of ẑ_i(ε_i) and Ŝ_i(ε_i)

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model

namespace NestedLogitVariants.General

variable {ι : Type*} {n : ℕ}

/-- The capacity used by the eligible products (weight `≤ ε`) that precede product `j` in index
order, which is revenue order since `r_{i1} ≥ … ≥ r_{in}`. -/
noncomputable def prefixLoad (I : Instance ι n) (i : ι) (ε : ℝ) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => k < j ∧ I.v i k ≤ ε), I.v i k

/-- The greedy solution `ẑ_i(ε)` of the continuous knapsack problem (11), pp. 23–24: fill the
knapsack of capacity `ε` with the eligible products (`v_{ij} ≤ ε`) in revenue order (ties broken by
index), taking each product fully while it fits and the next one fractionally; ineligible products
get `0`. -/
noncomputable def zhat (I : Instance ι n) (i : ι) (ε : ℝ) (j : Fin n) : ℝ :=
  if I.v i j ≤ ε then max 0 (min 1 ((ε - prefixLoad I i ε j) / I.v i j)) else 0

/-- `Ŝ_i(ε) = {j ∈ N : ẑ_{ij}(ε) = 1}`, p. 24. -/
noncomputable def Shat (I : Instance ι n) (i : ι) (ε : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => zhat I i ε j = 1)

end NestedLogitVariants.General


