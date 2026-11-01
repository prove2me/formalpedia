-- Prove2me | Definitions.Def_ShrinkingUCB_IsOptimalSet
-- name    : ShrinkingUCB_IsOptimalSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:17:29.35759+00:00
-- url     : https://prove2.me/theorems/3262202c-7964-4bb3-8038-e05fb683ecfc
-- title:
--   Optimal product set $S^*$
-- statement:
--   A set $S^*\subset[N]$ is an **optimal product set** for the size $K$ if $|S^*|=K$ and
--
--   $$
--   \sum_{i\in S}\mu(i)\le\sum_{i\in S^*}\mu(i)\qquad\text{for every }S\subset[N]\text{ with }|S|=K.
--   $$
--
--   That is, $S^*$ consists of $K$ products with the highest probabilities of positive sales. Such a set need not be unique. It is the benchmark in the definition of regret.
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, §2, p.9

import Definitions.Def_ShrinkingUCB_LinearSemiBandit

namespace ShrinkingUCB

/-- An optimal product set (arXiv:1903.07844v2, §2, p.9):
`S* ∈ arg max_{S ⊂ [N], |S| = K} ∑_{i ∈ S} µ(i)`. Optimal sets need not be unique. -/
def IsOptimalSet {d N : ℕ} (I : LinearSemiBandit d N) (K : ℕ) (S : Finset (Fin N)) : Prop :=
  S.card = K ∧ ∀ S' : Finset (Fin N), S'.card = K → ∑ i ∈ S', I.μ i ≤ ∑ i ∈ S, I.μ i

end ShrinkingUCB


