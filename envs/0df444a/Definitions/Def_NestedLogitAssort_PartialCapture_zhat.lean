-- Prove2me | Definitions.Def_NestedLogitAssort_PartialCapture_zhat
-- name    : NestedLogitAssort_PartialCapture_zhat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:43:07.673297+00:00
-- url     : https://prove2.me/theorems/3c011334-417a-4be2-b542-63e54456b79a
-- title:
--   Greedy solution $\hat z_i(\epsilon_i)$ of the continuous knapsack
-- statement:
--   For a nest $i$ and a capacity $\epsilon$, the greedy solution $\hat z_i(\epsilon)$ of (11) considers only the products with $v_{ij}\le\epsilon$ and fills the knapsack in order of decreasing revenue. Since the products are numbered so that $r_{i1}\ge\dots\ge r_{in}$, this is the order $j=1,2,\dots$. Writing
--
--   $$
--   p_j=\sum_{k<j,\ v_{ik}\le\epsilon}v_{ik}
--   $$
--
--   for the weight of the eligible products before $j$, the greedy gives
--
--   $$
--   \hat z_{ij}(\epsilon)=\begin{cases}0 & v_{ij}>\epsilon,\\ 1 & v_{ij}=0\le\epsilon,\\ \min\bigl\{1,\max\{0,(\epsilon-p_j)/v_{ij}\}\bigr\} & 0<v_{ij}\le\epsilon.\end{cases}
--   $$
--
--   This is the solution of (11) that the paper uses to build its candidate assortments.
--
--   **Formalization Note** Products of equal revenue are filled in index order. A product of weight $0$ uses no capacity and is taken fully.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, pp. 23–24 (unnumbered)

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_Instance

namespace NestedLogitAssort.PartialCapture

/-- **The greedy solution `ẑ_i(ϵ_i)` of the continuous knapsack (11).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, pp. 23–24 (unnumbered): "we can solve this problem by sorting the products with respect to
their revenues and filling the knapsack starting from the product with the largest revenue, as
long as we only consider the products whose preference weights do not exceed `ϵ_i`. We let
`ẑ_i(ϵ_i) = (ẑ_{i1}(ϵ_i), …, ẑ_{in}(ϵ_i))` be an optimal solution to problem (11) that we obtain
in this fashion."

The products are sorted by revenue (`r_{i1} ≥ … ≥ r_{in}`, p. 7), so the fill runs in index order
over the eligible products (`v_{ij} ≤ ϵ`). With `pre_j` the total weight of the eligible products
before `j`, an eligible product receives `min(1, max(0, (ϵ − pre_j)/v_{ij}))` (and `1` if
`v_{ij} = 0`), an ineligible one receives `0`.

**Formalization Note.** This closed form is the sequential fill in index order. Products of equal
revenue are filled in index order; this is one of the solutions "obtained in this fashion". A
product of weight `0` takes no capacity and is given `ẑ_{ij} = 1`. -/
noncomputable def zhat {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (ε : ℝ) (j : Fin n) : ℝ :=
  let pre : ℝ := ∑ k ∈ Finset.univ.filter (fun k => k < j ∧ I.v i k ≤ ε), I.v i k
  if I.v i j ≤ ε then
    (if I.v i j = 0 then 1 else min 1 (max 0 ((ε - pre) / I.v i j)))
  else 0

end NestedLogitAssort.PartialCapture


