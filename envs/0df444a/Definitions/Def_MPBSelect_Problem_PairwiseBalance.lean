-- Prove2me | Definitions.Def_MPBSelect_Problem_PairwiseBalance
-- name    : MPBSelect_Problem_PairwiseBalance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:51.521461+00:00
-- url     : https://prove2.me/theorems/80699c80-4eb7-4531-b2c1-ef7eeef9d4a6
-- title:
--   The pairwise balance condition (21) of Theorem 3
-- statement:
--   An allocation $\boldsymbol\alpha$ satisfies the **pairwise balance condition** if, for all $(i,\theta_b),(j,\theta_{b'})\in\Xi$,
--   $$
--   W_i(\theta_b)G_i(\theta_b)=W_j(\theta_{b'})G_j(\theta_{b'}),
--   $$
--   with $W$ the balance weights (17). That is, the weighted pairwise rate takes one common value over all of $\Xi$, across different parameters.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Theorem 3, p.17, (21)

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_Problem_Xi
import Definitions.Def_MPBSelect_Problem_W
import Definitions.Def_MPBSelect_Problem_G

namespace MPBSelect

/-- **Pairwise balance condition (21)** of Theorem 3.
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 3, (21),
p.17: "(Pairwise balance condition) For all (i,θb),(j,θb′) ∈ Ξ, {Wi(θb)} given in (17)
satisfies Wi(θb)Gi(θb) = Wj(θb′)Gj(θb′)."

The product `W_i(θ_b) G_i(θ_b)` takes the same value at every two pairs of `Ξ`, including
pairs at different parameters `θ_b ≠ θ_{b'}`. -/
def Problem.PairwiseBalance {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ) : Prop :=
  ∀ x ∈ P.Xi, ∀ x' ∈ P.Xi, P.W x.1 x.2 * P.G α x.1 x.2 = P.W x'.1 x'.2 * P.G α x'.1 x'.2

end MPBSelect


