-- Prove2me | Definitions.Def_JohnsonFlowShop_TwoStage_F
-- name    : JohnsonFlowShop_TwoStage_F
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:37:28.60607+00:00
-- url     : https://prove2.me/theorems/2c163a15-e868-450f-8272-11b8626f3491
-- title:
--   Johnson's function $F(S) = \max_u K_u$ (p. 63)
-- statement:
--   For $n \ge 1$ items and an order $\sigma$ (with $\sigma(k)$ the item in position $k$), Johnson's function is
--   $$
--   F(\sigma) = \max_{0 \le u \le n-1} K_u ,
--   $$
--   where $K_u$ are the quantities of the definition `K` (the paper's $F(S) = \max_{1 \le u \le n} K_u$). By the closed form of p. 62 it is the total idle time of machine 2 under the as-soon-as-possible schedule of $\sigma$, so minimizing $F$ over orders minimizes the total elapsed time.
--
--   **Formalization Note** The maximum is `Finset.sup'` over the nonempty set of positions, which is why the definition carries `[NeZero n]`.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 63, Two-stage production schedule ("Let F(S) = max_{1≤u≤n} K_u")

import Mathlib
import Definitions.Def_JohnsonFlowShop_Shared_K

namespace JohnsonFlowShop.TwoStage

/-- Johnson's objective `F(S) = max_{1 ≤ u ≤ n} K_u` for the order `σ` (requires `n ≥ 1`). -/
def F {n : ℕ} [NeZero n] (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (Shared.K A B σ)

end JohnsonFlowShop.TwoStage


