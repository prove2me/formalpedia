-- Prove2me | Definitions.Def_StaticProphetSec_gamma
-- name    : StaticProphetSec_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:53.221005+00:00
-- url     : https://prove2.me/theorems/e5fcb771-4566-4246-82d2-20408c14d299
-- title:
--   The constant $\gamma_k = 1 - e^{-k}k^k/k!$
-- statement:
--   For a positive integer $k$, the constant
--
--   $$\gamma_k = 1 - e^{-k}\frac{k^k}{k!}$$
--
--   equals $1-\mathbb P(\mathrm{Pois}(k)=k)$. It is the guarantee of the mission: $\gamma_1 = 1-1/e$, and $\gamma_k\to1$ as $k\to\infty$.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, (1), p.4

import Mathlib

open scoped Nat

namespace StaticProphetSec

/-- The constant `γ_k = 1 - e^{-k} k^k / k!`, equation (1) (Arnosti & Ma, Tight Guarantees for
Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, (1), p.4). -/
noncomputable def gamma (k : ℕ) : ℝ :=
  1 - Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k ! : ℝ)

end StaticProphetSec


