-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubmodularSetFunction
-- name    : DiscreteConvex_LConvexFunctionsD_SubmodularSetFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:27.483508+00:00
-- url     : https://prove2.me/theorems/7ef3e951-1c76-4fdb-9a23-e9d605845f0b
-- title:
--   SubmodularSetFunction
-- statement:
--   A set function $\rho:2^V\to\mathbb R\cup\{+\infty\}$ is submodular, with $\rho(\emptyset)=0$ and $\rho(V)<+\infty$ (the class $S[\mathbb R]$).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.104, Eq. (4.10)-(4.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.104, Eq. (4.10)-(4.11)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A set function `ρ : 2^V → R∪{+∞}` is submodular, with `ρ(∅)=0` and `ρ(V) < +∞` (the class
`S[R]`). -/
def SubmodularSetFunction (rho : Finset V → WithTop ℝ) : Prop :=
  rho ∅ = 0 ∧ rho Finset.univ ≠ ⊤ ∧
    ∀ X Y : Finset V, rho X + rho Y ≥ rho (X ∪ Y) + rho (X ∩ Y)

end DiscreteConvex.LConvexFunctionsD


