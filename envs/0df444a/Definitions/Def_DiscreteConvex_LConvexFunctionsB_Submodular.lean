-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_Submodular
-- name    : DiscreteConvex_LConvexFunctionsB_Submodular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:20:52.960647+00:00
-- url     : https://prove2.me/theorems/cf82c15e-2e53-4ff7-bc6e-d30bf8315e3e
-- title:
--   Submodular
-- statement:
--   A set function $\rho:2^V\to\mathbb R\cup\{+\infty\}$ is submodular.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.179, standard notion.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.179, standard notion

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A set function `ρ : 2^V → R∪{+∞}` is submodular. -/
def Submodular (rho : Finset V → WithTop ℝ) : Prop :=
  ∀ X Y : Finset V, rho X + rho Y ≥ rho (X ∪ Y) + rho (X ∩ Y)

end DiscreteConvex.LConvexFunctionsB


