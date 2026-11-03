-- Prove2me | Definitions.Def_DCAExtrap_extrap
-- name    : DCAExtrap_extrap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:33.910092+00:00
-- url     : https://prove2.me/theorems/4209bb13-c776-4a8a-a4c4-c8ce65dea367
-- title:
--   Extrapolated point $y^k = x^k + \beta_k(x^k - x^{k-1})$
-- statement:
--   Given iterates $(x^k)$ and extrapolation parameters $(\beta_k)$, the **extrapolated point** is
--
--   $$
--   y^k = x^k + \beta_k\,(x^k - x^{k-1}),
--   $$
--
--   with $x^{-1}=x^0$. DCAe linearizes $L\varphi-f$ at $y^k$.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, Algorithm 1, step 1, p.5

import Mathlib
import Definitions.Def_DCAExtrap_prev

namespace DCAExtrap

/-- **The extrapolated point** (Phan–Le Thi, arXiv:2106.04743v1, Algorithm 1 step 1, p.5):
`y^k = x^k + β_k (x^k − x^{k−1})`, with `x^{−1} = x^0` (`prev`). -/
def extrap {E : Type*} [AddCommGroup E] [Module ℝ E] (x : ℕ → E) (β : ℕ → ℝ) (k : ℕ) : E :=
  x k + β k • (x k - prev x k)

end DCAExtrap


