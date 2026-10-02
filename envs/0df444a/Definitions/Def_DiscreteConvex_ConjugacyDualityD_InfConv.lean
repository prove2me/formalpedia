-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_InfConv
-- name    : DiscreteConvex_ConjugacyDualityD_InfConv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:56:01.468381+00:00
-- url     : https://prove2.me/theorems/565f2272-f035-4145-989a-c63487879ea8
-- title:
--   InfConv
-- statement:
--   The integer infimal convolution $(g_1\square g_2)(p)=\inf\{g_1(p_1)+g_2(p_2):p_1+p_2=p\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, Eq. (6.43)-analogue, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, Eq. (6.43)-analogue, redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integer infimal convolution `(g1□g2)(p) = inf{g1(p1)+g2(p2) : p1+p2=p}`. -/
noncomputable def InfConv (g1 g2 : (V → ℤ) → WithTop ℝ) (p : V → ℤ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ L = g1 p1 + g2 p2}

end DiscreteConvex.ConjugacyDualityD


