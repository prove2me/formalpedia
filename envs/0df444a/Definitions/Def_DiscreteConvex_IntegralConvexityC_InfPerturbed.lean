-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_InfPerturbed
-- name    : DiscreteConvex_IntegralConvexityC_InfPerturbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:10:31.085981+00:00
-- url     : https://prove2.me/theorems/e1e9914f-bfc2-4ab3-a7b6-83968908fb7c
-- title:
--   Infimum of a linearly perturbed function
-- statement:
--   $\inf f[-p]=\inf_x\{f(x)-\langle p,x\rangle\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ToEReal3

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, citing `inf f[-p]`: the infimum value of a
linearly perturbed function, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `inf f[-p] = inf_x \{f(x) - ⟨p,x⟩\}`, valued in `EReal`. -/
noncomputable def InfPerturbed {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (p : Fin n → ℝ) : EReal :=
  sInf {v : EReal | ∃ x : Fin n → ℤ, v = ToEReal3 (f x) - ((∑ i, p i * (x i : ℝ) : ℝ) : EReal)}

end DiscreteConvex.IntegralConvexityC


