-- Prove2me | Definitions.Def_EzeunalaJiangKS_Signing_Dual
-- name    : EzeunalaJiangKS_Signing_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:02:50.382425+00:00
-- url     : https://prove2.me/theorems/6bc7722b-228a-487d-89bc-00b6269149e9
-- title:
--   Stationarity relations and chosen dual pair
-- statement:
--   At the chosen primal optimizer, dual matrices are positive definite and satisfy
--   $$\operatorname{Tr}(P+Q)=1,\quad P=\varepsilon X^2+X\eta_x(Q)X,\quad Q=\varepsilon Y^2+Y\eta_x(P)Y.$$
--   The chosen pair satisfies these equations if a pair exists and is zero otherwise. No structure supplies existence, uniqueness, or optimality as an axiom.
--
--   These are the stationary multipliers used in variations. Their existence, uniqueness, and the tightness of primal constraints are proof obligations from the source's optimality analysis. The predicates record equations, while the chosen objects are computed specifications from the data.
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), §4.1, (9)–(10), printed p. 8 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_Potential

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

abbrev PairMat (d : ℕ) := CMat d × CMat d

def isDual {N d : ℕ} (A : Fin N → CMat d) (x : State N) (X Y : CMat d)
    (pq : PairMat d) : Prop :=
  pq.1.PosDef ∧ pq.2.PosDef ∧ tr (pq.1 + pq.2) = 1 ∧
    pq.1 = epsilon A • (X * X) + X * eta A x pq.2 * X ∧
    pq.2 = epsilon A • (Y * Y) + Y * eta A x pq.1 * Y

def dual {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) : PairMat d :=
  let z := optimizer A x₀ x
  if h : ∃ pq, isDual A x z.2.1 z.2.2 pq then Classical.choose h else (0, 0)

end EzeunalaJiangKS.Signing


