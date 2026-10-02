-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_RhoTilde
-- name    : DiscreteConvex_AlgorithmsB_RhoTilde
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:58:44.472713+00:00
-- url     : https://prove2.me/theorems/9494c506-be01-4b7b-b6eb-46426a367a25
-- title:
--   RhoTilde
-- statement:
--   $\tilde\rho(Y)=\rho(\Gamma(Y)\cup Z)-\rho(Z)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, preceding Eq. (10.26).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, preceding Eq. (10.26)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_GammaSet

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `ρ̃(Y) = ρ(Γ(Y)∪Z) - ρ(Z)`. -/
def RhoTilde {U : Type*} [DecidableEq U] (rho : Finset V → ℤ) (Gamma : U → Finset V) (Z : Finset V)
    (Y : Finset U) : ℤ :=
  rho (GammaSet Gamma Y ∪ Z) - rho Z

end DiscreteConvex.AlgorithmsB


