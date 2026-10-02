-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerLower
-- name    : DiscreteConvex_NetworkFlows_IsIntegerLower
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:14:03.249926+00:00
-- url     : https://prove2.me/theorems/ec342672-2710-4773-990d-0416b2adf234
-- title:
--   Integer-valuedness of an $\mathbb R\cup\{-\infty\}$-valued function
-- statement:
--   An $\mathbb R \cup \{-\infty\}$-valued function is **integer valued** if every finite value it takes is an integer.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.248.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.248

import Mathlib

/-!
Integer-valuedness of a `ℝ ∪ {-∞}`-valued function, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- A `ℝ ∪ {-∞}`-valued function is **integer valued** if every finite value it takes is an
integer. -/
def IsIntegerLower {α : Type*} (g : α → WithBot ℝ) : Prop :=
  ∀ a : α, ∀ r : ℝ, g a = (r : WithBot ℝ) → ∃ n : ℤ, (n : ℝ) = r

end DiscreteConvex.NetworkFlows


