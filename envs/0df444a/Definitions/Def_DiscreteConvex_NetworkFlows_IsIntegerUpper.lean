-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerUpper
-- name    : DiscreteConvex_NetworkFlows_IsIntegerUpper
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:14:06.733628+00:00
-- url     : https://prove2.me/theorems/a99a35b8-d23f-410d-ae07-06a5bf8fe870
-- title:
--   Integer-valuedness of an $\mathbb R\cup\{+\infty\}$-valued function
-- statement:
--   An $\mathbb R \cup \{+\infty\}$-valued function is **integer valued** if every finite value it takes is an integer.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.248.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.248

import Mathlib

/-!
Integer-valuedness of a `ℝ ∪ {+∞}`-valued function, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- A `ℝ ∪ {+∞}`-valued function is **integer valued** if every finite value it takes is an
integer. -/
def IsIntegerUpper {α : Type*} (g : α → WithTop ℝ) : Prop :=
  ∀ a : α, ∀ r : ℝ, g a = (r : WithTop ℝ) → ∃ n : ℤ, (n : ℝ) = r

end DiscreteConvex.NetworkFlows


