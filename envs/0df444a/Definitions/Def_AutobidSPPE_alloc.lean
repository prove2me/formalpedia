-- Prove2me | Definitions.Def_AutobidSPPE_alloc
-- name    : AutobidSPPE_alloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:03.655481+00:00
-- url     : https://prove2.me/theorems/7010c0c4-a79c-468b-a00b-be4dad69c9b1
-- title:
--   Allocation indicator $x_i(\alpha)$
-- statement:
--   The **allocation indicator** of bidder $i$ at multipliers $\alpha$ and value profile $v$ is
--   $$
--   x_i(\alpha) = \begin{cases} 1 & \text{if } i \text{ is the winner},\\ 0 & \text{otherwise}.\end{cases}
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.1, p.4; Table 1, p.9

import Mathlib
import Definitions.Def_AutobidSPPE_winner

namespace AutobidSPPE

/-- The allocation indicator `xᵢ(α) ∈ {0, 1}` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.1, p.4; Table 1, p.9): `1` if
bidder `i` wins the item at value profile `v`, else `0`. -/
noncomputable def alloc {n : ℕ} (tie : TieRule n) (α v : Fin n → ℝ) (i : Fin n) : ℝ :=
  if winner tie α v = i then 1 else 0

end AutobidSPPE


