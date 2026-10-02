-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_ModifiedFlow
-- name    : DiscreteConvex_NetworkFlowsC_ModifiedFlow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:58.117369+00:00
-- url     : https://prove2.me/theorems/f732cbb7-11a7-4ba6-9a81-8296b4d48363
-- title:
--   ModifiedFlow
-- statement:
--   The modified flow $\bar\xi$, obtained by canceling a cycle.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, Eq. (9.75).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, Eq. (9.75)

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The modified flow `ξ̄` of Eq. (9.75), obtained by canceling the cycle `a`. -/
def ModifiedFlow (tail head : A → V) (k : ℕ) (a : Fin (k+1) → (A ⊕ A ⊕ (V × V))) (xi : A → ℤ)
    (x : A) : ℤ :=
  if (∃ i, a i = Sum.inl x) then xi x + 1
  else if (∃ i, a i = Sum.inr (Sum.inl x)) then xi x - 1
  else xi x

-- ===== Theorems =====

end DiscreteConvex.NetworkFlowsC


