-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_RhoP
-- name    : DiscreteConvex_AlgorithmsC_RhoP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:19:10.992724+00:00
-- url     : https://prove2.me/theorems/9cc6a2fe-e31d-431a-82e1-b34c573842c0
-- title:
--   RhoP
-- statement:
--   $\rho_p(X)=g(p+\chi_X)-g(p)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.305, Eq. (10.32).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.305, Eq. (10.32)

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `ρ_p(X) = g(p+χ_X) - g(p)`, Eq. (10.32). -/
def RhoP (g : (V → ℤ) → WithTop ℝ) (p : V → ℤ) (X : Finset V) : WithTop ℝ :=
  g (fun v => p v + (if v ∈ X then (1:ℤ) else 0)) - g p

-- ===== Domain-size measures for L-convex functions (§10.3.1) =====

end DiscreteConvex.AlgorithmsC


