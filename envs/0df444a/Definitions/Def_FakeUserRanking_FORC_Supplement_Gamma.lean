-- Prove2me | Definitions.Def_FakeUserRanking_FORC_Supplement_Gamma
-- name    : FakeUserRanking_FORC_Supplement_Gamma
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:33:04.340442+00:00
-- url     : https://prove2.me/theorems/ef9811b8-d27f-4092-8123-8708f59478b5
-- title:
--   (13), p. 22 — FAR's sample threshold γ_{j,i}
-- statement:
--   The number of samples after which FAR can order two products.
--
--   For products $i,j$ with $i>j$ (so $\mu_j>\mu_i$), with gap $\Delta_{j,i}=\mu_j-\mu_i$ and $\delta=1/(nT)$,
--
--   $$\gamma_{j,i}=\max\left\{\frac{64\log(2nT/\delta)}{\Delta_{j,i}^2},\;\frac{8F}{\Delta_{j,i}}\right\}.\qquad(13)$$
--
--   Once both $\eta_{i,t}$ and $\eta_{j,t}$ reach $\gamma_{j,i}$, both windows (9) are at most $\Delta_{j,i}/4$, which is what Lemma 3 uses to show that FAR's graph then contains the edge $(i,j)$.
--
--   **Formalization Note** The definition is written for every pair of products; it is used only for pairs with $\mu_j>\mu_i$. Logarithms are natural, and products are `Fin n`, indexed from $0$.
--
--   Differences from the source:
--   - encoding: Products, positions and rounds use 1-based indices → Fin indices are 0-based; the state after t rounds uses the first t observations; reason: Relabelling preserves every source instance and round.
--   - encoding: Equation (13) defines γ for i > j and positive gaps → gamma13 is a total real function on all pairs and all natural n,T,F; reason: Only positive-gap pairs with n,T ≥ 1 are used by the theorems. Out-of-domain values from total division are not source claims.
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 22, (13)

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Supplement_FAR

namespace FakeUserRanking.FORC.Supplement

variable {n : ℕ}

/-- The threshold (13), p. 22, for products `j` better than `i`:
`γ_{j,i} = max{64 log(2nT/δ)/Δ²_{j,i}, 8F/Δ_{j,i}}` with `δ = 1/(nT)` and `Δ_{j,i} = μ_j − μ_i`. -/
noncomputable def gamma13 (T F : ℕ) (inst : Instance n) (j i : Fin n) : ℝ :=
  max (64 * Real.log (2 * n * T / farDelta n T) / gap inst j i ^ 2) (8 * (F : ℝ) / gap inst j i)

end FakeUserRanking.FORC.Supplement


