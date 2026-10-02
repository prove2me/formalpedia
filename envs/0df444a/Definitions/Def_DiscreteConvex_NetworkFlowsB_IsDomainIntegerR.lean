-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDomainIntegerR
-- name    : DiscreteConvex_NetworkFlowsB_IsDomainIntegerR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:07.567086+00:00
-- url     : https://prove2.me/theorems/65b2957e-d9b2-4c47-bdbe-43b96933c18d
-- title:
--   IsDomainIntegerR
-- statement:
--   $f:\mathbb R^V\to\mathbb R\cup\{+\infty\}$ has integer effective domain (a "primal integral" boundary cost).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261, notation M[Z|R→R].)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261, notation M[Z|R→R]

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `f : Rⱽ → R ∪ {+∞}` has integer effective domain (a "primal integral" boundary cost). -/
def IsDomainIntegerR (f : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℝ, f x ≠ ⊤ → ∀ v, ∃ k : ℤ, x v = (k : ℝ)

end DiscreteConvex.NetworkFlowsB


