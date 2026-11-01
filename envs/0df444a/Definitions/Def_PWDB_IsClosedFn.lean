-- Prove2me | Definitions.Def_PWDB_IsClosedFn
-- name    : PWDB_IsClosedFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:12.628694+00:00
-- url     : https://prove2.me/theorems/1f901e6b-6ec3-4b3a-b453-a4fdbe92a6e1
-- title:
--   Closed extended-real function (Rockafellar's sense)
-- statement:
--   Let $X$ be a topological space and $g : X \to \overline{\mathbb R}$. The function $g$ is **closed** if it is lower semicontinuous and either $g(x) > -\infty$ for all $x$, or $g(x) = -\infty$ for all $x$.
--
--   Both constant functions $+\infty$ and $-\infty$ are closed. This is the notion used in Propositions C.5 and C.7, which do not assume properness.
--
--   **Formalization Note** Values in `EReal`.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Appendix A, p.39

import Mathlib

namespace PWDB

/-- **Closed function** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Appendix A, p.39):
"`f` is closed if `f` is lower semicontinuous and either `f(x) > −∞` for all `x` or `f(x) = −∞`
for all `x`."

`IsClosedFn g` holds when `g` is lower semicontinuous and either never takes the value `−∞` or is
identically `−∞`.

**Formalization Note** Values in `EReal`. This is Rockafellar's notion of a closed function, so the
constant functions `+∞` and `−∞` are both closed; this matters for Propositions C.5 and C.7, which
do not assume properness. The domain is any topological space (the paper's is `ℝ^d`). -/
def IsClosedFn {X : Type*} [TopologicalSpace X] (g : X → EReal) : Prop :=
  LowerSemicontinuous g ∧ ((∀ x, g x ≠ ⊥) ∨ (∀ x, g x = ⊥))

end PWDB


