-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_LinFunc
-- name    : DiscreteConvex_IntegralConvexityB_LinFunc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:59:24.367164+00:00
-- url     : https://prove2.me/theorems/a5e9e942-911b-4705-82b7-60ea748e81c6
-- title:
--   Affine functional on (V to R) x R
-- statement:
--   $\mathrm{LinFunc}(w,c,p)=\langle w,p_1\rangle+c\,p_2$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.10).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.10)

import Mathlib

/-!
An affine functional on `(V → ℝ) × ℝ`, used to describe polyhedra (Murota, *Discrete Convex
Analysis*, SIAM 2003, p.98, Eq. (3.10)), in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `LinFunc w c p = ⟨w, p.1⟩ + c·p.2`, a linear functional on `(V → ℝ) × ℝ` used to describe a
half-space in Eq. (3.10)'s style. -/
def LinFunc {V : Type*} [Fintype V] (w : V → ℝ) (c : ℝ) (p : (V → ℝ) × ℝ) : ℝ :=
  dotProduct w p.1 + c * p.2

end DiscreteConvex.IntegralConvexityB


