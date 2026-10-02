-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_FromEReal
-- name    : DiscreteConvex_AlgorithmsC_FromEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:18:59.040259+00:00
-- url     : https://prove2.me/theorems/1822b64b-510c-4d53-8307-8d2a45ae93bc
-- title:
--   FromEReal
-- statement:
--   The projection $\mathbb R\cup\{\pm\infty\}\to\mathbb R\cup\{+\infty\}$ sending $-\infty$ to the junk value $+\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The projection `R∪{±∞} → R∪{+∞}` sending `-∞` to the junk value `+∞`. -/
def FromEReal (v : EReal) : WithTop ℝ := WithBot.unbotD ⊤ v

end DiscreteConvex.AlgorithmsC


