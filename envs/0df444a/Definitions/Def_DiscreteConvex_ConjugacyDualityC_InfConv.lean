-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConv
-- name    : DiscreteConvex_ConjugacyDualityC_InfConv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:14.547737+00:00
-- url     : https://prove2.me/theorems/d9dff8d9-4405-4df3-b90f-d6973246af0e
-- title:
--   InfConv
-- statement:
--   The integer infimal convolution $(g_1\square g_2)(p)=\inf\{g_1(p_1)+g_2(p_2):p_1+p_2=p\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, Eq. (6.43)-analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, Eq. (6.43)-analogue

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integer infimal convolution `(g1□g2)(p) = inf{g1(p1)+g2(p2) : p1+p2=p}`. -/
noncomputable def InfConv (g1 g2 : (V → ℤ) → WithTop ℝ) (p : V → ℤ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ L = g1 p1 + g2 p2}

end DiscreteConvex.ConjugacyDualityC


