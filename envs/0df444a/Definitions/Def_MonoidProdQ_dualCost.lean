-- Prove2me | Definitions.Def_MonoidProdQ_dualCost
-- name    : MonoidProdQ_dualCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:42:52.658038+00:00
-- url     : https://prove2.me/theorems/a605fc8d-291c-456a-b8f1-00dee32df231
-- title:
--   Cost of an all-pairs dual (Eq. (4))
-- statement:
--   The **cost** of a family of vectors $u_{x,i},v_{y,i}$ indexed by a finite promise domain $D$ and positions $i\in I$ is
--
--   $$\max\Big\{\max_{x\in D}\sum_i\|u_{x,i}\|^2,\ \max_{y\in D}\sum_i\|v_{y,i}\|^2\Big\}.$$
--
--   A dual "of cost $T$" is one whose cost is at most $T$. Each maximum is $0$ when $D$ is empty.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Eq. (4), p.25

import Mathlib

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Eq. (4), p.25: the cost of an all-pairs dual,
`max { maxₓ Σᵢ ‖u_{x,i}‖², max_y Σᵢ ‖v_{y,i}‖² }`; a dual "of cost T" is one with this
quantity at most `T`. Each maximum is over the finite promise domain (`0` if it is empty). -/
noncomputable def dualCost {I Sig : Type*} [Fintype I] {D : Finset (I → Sig)} {d : ℕ}
    (u v : D → I → EuclideanSpace ℂ (Fin d)) : NNReal :=
  max (Finset.univ.sup fun x : D => ∑ i, ‖u x i‖₊ ^ 2)
    (Finset.univ.sup fun y : D => ∑ i, ‖v y i‖₊ ^ 2)

end MonoidProdQ


