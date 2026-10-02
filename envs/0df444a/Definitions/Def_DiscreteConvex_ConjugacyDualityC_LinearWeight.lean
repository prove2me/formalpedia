-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_LinearWeight
-- name    : DiscreteConvex_ConjugacyDualityC_LinearWeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:12.101908+00:00
-- url     : https://prove2.me/theorems/ed2f8618-bd08-48dd-a553-e4046496711d
-- title:
--   LinearWeight
-- statement:
--   $g[p](x) = g(x) - \langle p,x\rangle$ for integer-domain $g$ and real weight $p$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.69)

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g[p](x) = g(x) - ⟨p,x⟩` for integer-domain `g` and real weight `p`. -/
def LinearWeight (g : (V → ℤ) → WithTop ℝ) (p : V → ℝ) : (V → ℤ) → WithTop ℝ :=
  fun x => g x + (((-(∑ v, p v * (x v : ℝ)) : ℝ)) : WithTop ℝ)

end DiscreteConvex.ConjugacyDualityC


