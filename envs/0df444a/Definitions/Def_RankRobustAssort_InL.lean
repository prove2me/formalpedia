-- Prove2me | Definitions.Def_RankRobustAssort_InL
-- name    : RankRobustAssort_InL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:21.473041+00:00
-- url     : https://prove2.me/theorems/8bd589fe-3004-4413-8d90-dcec2a772fbe
-- title:
--   Tuples of top products $\mathcal L$
-- statement:
--   A tuple of products $(i_1,\dots,i_M)$ belongs to
--
--   $$
--   \mathcal L=\Big\{(i_1,\dots,i_M)\in S_1\times\dots\times S_M:\ \bigcap_{m\in\mathcal M}\mathcal D_{i_m}(S_m)\ne\emptyset\Big\}
--   $$
--
--   when a single ranking makes $i_m$ the most preferred product of $S_m$ for every past assortment $m$ simultaneously. The tuples in $\mathcal L$ index the variables of the linear program (2).
--
--   **Formalization Note.** A tuple is a function from $\mathrm{Fin}\,M$ to products. Membership in $S_1\times\dots\times S_M$ is implied by "$i_m$ is most preferred in $S_m$". For $M=0$ the empty tuple belongs to $\mathcal L$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Definition 3, p.15

import Mathlib
import Definitions.Def_RankRobustAssort_Problem
import Definitions.Def_RankRobustAssort_IsTop

namespace RankRobustAssort

/-- A tuple of products `(i₁,…,i_M)` lies in
`ℒ ≜ {(i₁,…,i_M) ∈ S₁ × ⋯ × S_M : ⋂_{m∈ℳ} 𝒟_{i_m}(S_m) ≠ ∅}`: some ranking makes `i_m` the most
preferred product of `S_m` for every past assortment `m` simultaneously.

Sturt, arXiv:2112.05010v4, Definition 3, p.15.

Formalization Note: a tuple is a function `t : Fin M → Fin (n+1)` (`t m` is the paper's
`i_{m+1}`). `IsTop σ (S m) (t m)` already contains `t m ∈ S m`, so membership in
`S₁ × ⋯ × S_M` is implied. For `M = 0` the empty tuple is in `ℒ` (the empty intersection is `Σ`). -/
def InL {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1)) : Prop :=
  ∃ σ : Equiv.Perm (Fin (n + 1)), ∀ m, IsTop σ (P.S m) (t m)

end RankRobustAssort


