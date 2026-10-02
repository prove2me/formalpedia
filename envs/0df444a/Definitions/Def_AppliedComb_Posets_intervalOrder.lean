-- Prove2me | Definitions.Def_AppliedComb_Posets_intervalOrder
-- name    : AppliedComb_Posets_intervalOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:05:31.578198+00:00
-- url     : https://prove2.me/theorems/bd21171d-702b-4b3e-a280-fd5d98b3785a
-- title:
--   Interval orders, the poset 2 + 2, and excluded subposets (Sections 6.2 and 6.6)
-- statement:
--   Let $\mathbf P = (X, P)$ be a partially ordered set, represented by a type $\alpha$ with a partial order.
--
--   $\mathbf P$ is an **interval order** if there are real numbers $a_x \le b_x$ for each $x \in X$ (the closed interval $I(x) = [a_x, b_x]$; degenerate intervals with $a_x = b_x$ are allowed) such that for all $x, y \in X$
--   $$x < y \text{ in } \mathbf P \iff b_x < a_y \text{ in } \mathbb R.$$
--
--   For $n \ge 1$, $\mathbf n$ is the chain on $\{0, 1, \dots, n-1\}$. For posets $\mathbf P$, $\mathbf Q$ on disjoint ground sets, $\mathbf P + \mathbf Q$ is the poset on the union in which $z \le w$ exactly when $z, w$ lie in the same summand and $z \le w$ there. In particular $\mathbf 2 + \mathbf 2$ is the four-point poset with $a < b$, $c < d$ and no other strict relations.
--
--   $\mathbf P$ **excludes** $\mathbf Q$ if no subposet of $\mathbf P$ is isomorphic to $\mathbf Q$, that is, if there is no injective map $f$ from the ground set of $\mathbf Q$ into $X$ with $q \le q'$ in $\mathbf Q$ if and only if $f(q) \le f(q')$ in $\mathbf P$.
--
--   **Formalization Note.** `TwoPlusTwo` is `Fin 2 ⊕ Fin 2` with Mathlib's disjoint-sum order (`Sum.LiftRel`, not the lexicographic sum `⊕ₗ`), and `Excludes α β` is `IsEmpty (β ↪o α)` (no order embedding). `IsIntervalOrder α` asks for functions `a b : α → ℝ` with `a x ≤ b x` and `x < y ↔ b x < a y` for all `x y`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 119 (isomorphism, excludes), p. 128 (interval order; the chain n; P + Q), p. 129 (2 + 2)

import Mathlib

namespace AppliedComb.Posets

/-- Interval order (Keller & Trotter, p. 128): there is an assignment `x ↦ [a x, b x]` of
closed real intervals (degenerate intervals `a x = b x` allowed) such that for all `x y`,
`x < y` in the poset if and only if `b x < a y` in `ℝ`. -/
def IsIntervalOrder (α : Type*) [PartialOrder α] : Prop :=
  ∃ a b : α → ℝ, (∀ x, a x ≤ b x) ∧ ∀ x y : α, x < y ↔ b x < a y

/-- The poset `2 + 2` (Keller & Trotter, pp. 128–129): the disjoint sum of two copies of the
2-element chain `2 = {0, 1}`. Mathlib's order on `Fin 2 ⊕ Fin 2` is the disjoint-sum order
(`Sum.LiftRel`): `z ≤ w` iff both lie in the same summand and `z ≤ w` there. -/
abbrev TwoPlusTwo : Type := Fin 2 ⊕ Fin 2

/-- `P` excludes `Q` (Keller & Trotter, p. 119): no subposet of `P` is isomorphic to `Q`,
i.e. there is no order embedding of `Q` into `P`. -/
def Excludes (α β : Type*) [PartialOrder α] [PartialOrder β] : Prop :=
  IsEmpty (β ↪o α)

end AppliedComb.Posets


