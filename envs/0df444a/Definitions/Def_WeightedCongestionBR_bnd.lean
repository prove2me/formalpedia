-- Prove2me | Definitions.Def_WeightedCongestionBR_bnd
-- name    : WeightedCongestionBR_bnd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:00.078683+00:00
-- url     : https://prove2.me/theorems/47df0703-d300-4dd1-99b3-7ba36b678ac1
-- title:
--   Boundaries $b_i=g^{-i}c_{\max}$, Line 3
-- statement:
--   For $i\ge 0$,
--
--   $$
--   b_i=g^{-i}\,c_{\max},
--   $$
--
--   so $c_{\max}=b_0>b_1>\dots>b_m$. In phase $i$ the algorithm treats costs in $[b_i,\infty)$ as large and costs in $[b_{i+1},b_i)$ as small.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Algorithm 1, Line 3, p.14

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_cmax
import Definitions.Def_WeightedCongestionBR_gConst
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- The cost boundaries `b_i := g^{-i} c_max` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Algorithm 1, Line 3, p.14); `b_0 = c_max`.

**Formalization Note** Defined for every `i : ℕ`; the algorithm uses `0 ≤ i ≤ m`. -/
noncomputable def bnd {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) (i : ℕ) : ℝ :=
  cmax G sinit / gConst n d m ^ i

end WeightedCongestionBR


