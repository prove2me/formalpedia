-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRho
-- name    : DiscreteConvex_LConvexFunctionsD_InducedRho
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:37.249082+00:00
-- url     : https://prove2.me/theorems/92114e26-5950-4915-9377-9af1e76d1dc0
-- title:
--   InducedRho
-- statement:
--   The set function $\rho_g(X)=g(\chi_X)$ induced by a positively homogeneous real-domain function, Eq. (7.35).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, Eq. (7.35).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, Eq. (7.35)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The set function `ρ_g(X) = g(χ_X)` induced by a positively homogeneous real-domain
function, Eq. (7.35). -/
def InducedRho (g : (V → ℝ) → WithTop ℝ) (X : Finset V) : WithTop ℝ :=
  g (fun v => if v ∈ X then (1 : ℝ) else 0)

end DiscreteConvex.LConvexFunctionsD


