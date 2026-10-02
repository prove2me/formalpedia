-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_RhoTilde
-- name    : DiscreteConvex_AlgorithmsC_RhoTilde
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:24:52.0425+00:00
-- url     : https://prove2.me/theorems/f8a74277-cabe-4708-b26a-9de99318e1c6
-- title:
--   RhoTilde
-- statement:
--   $\tilde\rho(Y)=\rho(\Gamma(Y)\cup Z)-\rho(Z)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_GammaSet

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `ρ̃(Y) = ρ(Γ(Y)∪Z) - ρ(Z)`. -/
def RhoTilde {U : Type*} [DecidableEq U] (rho : Finset V → ℤ) (Gamma : U → Finset V) (Z : Finset V)
    (Y : Finset U) : ℤ :=
  rho (GammaSet Gamma Y ∪ Z) - rho Z

end DiscreteConvex.AlgorithmsC


