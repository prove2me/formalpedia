-- Prove2me | Definitions.Def_RankOneBTF_Prop7Cond1
-- name    : RankOneBTF_Prop7Cond1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:04.746246+00:00
-- url     : https://prove2.me/theorems/4df23aa6-a5e9-4ead-a79a-3c9451de5903
-- title:
--   Condition 1 of Proposition 7: every zero coordinate meets a corrupted entry
-- statement:
--   **Condition 1 of Proposition 7.** For each $i\in[n]$ with $\bar x_i=0$, $F^{x,i}>0$; for each $j\in[m]$ with $\bar y_j=0$, $F^{y,j}>0$; and for each $k\in[l]$ with $\bar z_k=0$, $F^{z,k}>0$.
--
--   It is a hypothesis of Propositions 10 and 11 and the event $A^0$ of Claim 1.
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §7.1, p.16, Proposition 7, Condition 1; p.20 (event A⁰)

import Mathlib
import Definitions.Def_RankOneBTF_Tx

namespace RankOneBTF

/-- **Condition 1 of Proposition 7** (arXiv:2202.07053v3, p.16): "For each i ∈ [n] with
x̄_i = 0, we have F^{x,i} > 0, for each j ∈ [m] with ȳ_j = 0, we have F^{y,j} > 0, and for each
k ∈ [l] with z̄_k = 0, we have F^{z,k} > 0." It is a hypothesis of Propositions 10 and 11, and
the event `A⁰` of Claim 1 (p.20). -/
def Prop7Cond1 {n m l : ℕ} (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) : Prop :=
  (∀ i, xb i = false → 0 < FxTot xb yb zb G i) ∧
  (∀ j, yb j = false → 0 < FyTot xb yb zb G j) ∧
  (∀ k, zb k = false → 0 < FzTot xb yb zb G k)

end RankOneBTF


