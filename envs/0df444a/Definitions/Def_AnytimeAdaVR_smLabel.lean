-- Prove2me | Definitions.Def_AnytimeAdaVR_smLabel
-- name    : AnytimeAdaVR_smLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:57.331247+00:00
-- url     : https://prove2.me/theorems/d8147dd2-77bc-4883-84a6-6f404d4d9ded
-- title:
--   Reporting label $\ell_r$ of each local query of an S or M path
-- statement:
--   A block of an S path costs $b$ queries and a block of an M path costs $2b-1$ (one query at $t=1$, then a pair of queries at each later step). At the start of each block a **reporting label** is fixed: the block's starting point if $b=2$, and the stored point $Y$ if $b>2$. Every local query of the block, including both queries of an M pair and the last query, carries this label; the stored point is replaced only after the block's last query.
--
--   $\ell_r$ is the label of local query $r\ge1$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5.1, pp.7–8

import Mathlib
import Definitions.Def_AnytimeAdaVR_smState__9c32e5

namespace AnytimeAdaVR

/-- **The reporting label of each local query of an S or M path.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §5.1, pp.7–8: "At the
start of a block, fix a reporting label equal to its starting point if b = 2, or the stored Y if
b > 2. … Assign this fixed label to every individual query of the block, including both queries of
an M pair and the final query of the block. Only after processing that last label may the new Y
replace the stored point." and "The block uses b queries for S and 2b − 1 for M."

`smLabel k g xinit ξ r` is the label `ℓ_r` of local query `r ≥ 1`: the label of the block containing
query `r`, where block `j` costs `b_j` queries (S) or `2b_j − 1` queries (M) and the blocks are
executed in order.

**Formalization Note.** The block containing query `r` is the number of blocks completed before
it, i.e. the number of `j` with `cost_0 + ⋯ + cost_j < r` (all such `j` are `< r`, as costs are
`≥ 1`). Local query counts start at `1`; `r = 0` returns the first block's label. -/
noncomputable def smLabel {d : ℕ} {Ξ : Type*} (k : SMKind)
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (xinit : EuclideanSpace ℝ (Fin d)) (ξ : ℕ → Ξ) (r : ℕ) : EuclideanSpace ℝ (Fin d) :=
  let st := smState k g xinit ξ
  let cost : ℕ → ℕ := fun j =>
    match k with
    | .S => (st j).b
    | .M => 2 * (st j).b - 1
  let cum : ℕ → ℕ := fun J => ∑ j ∈ Finset.range J, cost j
  let j := ((Finset.range r).filter (fun j => cum (j + 1) < r)).card
  if (st j).b = 2 then (st j).x else (st j).Y

end AnytimeAdaVR


