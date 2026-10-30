-- Prove2me | Definitions.Def_NestedLogitAssort_General_pre
-- name    : NestedLogitAssort_General_pre
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:49:00.936586+00:00
-- url     : https://prove2.me/theorems/9f75b01f-b043-4199-a6da-83c8f5afce09
-- title:
--   Capacity used by the greedy fill before a product
-- statement:
--   For a nest $i$, a capacity $\epsilon$ and a product $j$, this is
--
--   $$
--   \mathrm{pre}_{ij}(\epsilon)=\sum\{v_{il}:\ l<j,\ v_{il}\le\epsilon\},
--   $$
--
--   the total preference weight of the products preceding $j$ in revenue order whose weights do not exceed $\epsilon$. It is the capacity the greedy fill of the continuous knapsack (11) has used, if all of them fit, before it reaches product $j$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 5, pp. 23–24

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Instance

namespace NestedLogitAssort.General

/-- **Capacity used by the greedy fill of (11) before product `j`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 5, pp. 23–24 (unnumbered): the greedy solution of the continuous knapsack (11)
fills the products whose preference weights do not exceed `ϵ_i`, starting from the product with
the largest revenue.

`pre I i ε j = ∑ {v_{il} : l < j, v_{il} ≤ ϵ}` is the total weight of the eligible products that
precede `j` in revenue (index) order. -/
noncomputable def pre {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (ε : ℝ) (j : Fin n) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l => l < j ∧ I.v i l ≤ ε), I.v i l

end NestedLogitAssort.General


