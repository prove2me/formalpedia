-- Prove2me | Definitions.Def_PWDB_IsConvexFn
-- name    : PWDB_IsConvexFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:13.788293+00:00
-- url     : https://prove2.me/theorems/203f00b5-3ea8-45e7-bf72-b7a3026073be
-- title:
--   Convex extended-real function (convex epigraph)
-- statement:
--   Let $X$ be a real vector space and $g : X \to \overline{\mathbb R}$. Its epigraph is $\operatorname{epi}(g) = \{(x,\tau) \in X \times \mathbb R \mid g(x) \le \tau\}$, and $g$ is **convex** if $\operatorname{epi}(g)$ is a convex set.
--
--   No properness is imposed; $g$ may take the values $\pm\infty$.
--
--   **Formalization Note** Values in `EReal`; Mathlib's `ConvexOn` does not apply to `EReal`-valued functions.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Appendix A, p.39 (epigraph)

import Mathlib

namespace PWDB

/-- **Convex extended-real function** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Appendix A,
p.39, with the epigraph `epi(f) = {(x, τ) ∈ ℝ^{dx} × ℝ | f(x) ≤ τ}` defined there).

`IsConvexFn g` says that the epigraph `{(x, τ) | g x ≤ τ}` of `g` is a convex subset of `X × ℝ`.

**Formalization Note** Values in `EReal`, so `g` may take `+∞` and `−∞`; Mathlib's `ConvexOn`
does not apply because `EReal` is not a module. Convexity of the epigraph is the standard
definition of convexity of an extended-real function (Rockafellar 1970, §4), and it imposes no
properness. -/
def IsConvexFn {X : Type*} [AddCommGroup X] [Module ℝ X] (g : X → EReal) : Prop :=
  Convex ℝ {p : X × ℝ | g p.1 ≤ (p.2 : EReal)}

end PWDB


