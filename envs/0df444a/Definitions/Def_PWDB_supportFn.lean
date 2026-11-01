-- Prove2me | Definitions.Def_PWDB_supportFn
-- name    : PWDB_supportFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:16.511204+00:00
-- url     : https://prove2.me/theorems/79bc9fdf-f62b-4ae5-aed4-6f312148c9a0
-- title:
--   Support function $\delta^*_S$
-- statement:
--   The **support function** of a set $S$ in a real inner product space $X$ is
--   $$
--   \delta^*_S(w) = \sup_{x \in S} \langle x, w\rangle .
--   $$
--   It is $-\infty$ for $S = \emptyset$.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Appendix A, p.39

import Mathlib

open scoped InnerProductSpace

namespace PWDB

/-- **Support function** of a set (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Appendix A, p.39):
"The support function `δ∗_X : ℝ^{dx} → R̄` of a set `X ⊆ ℝ^{dx}` is defined through
`δ∗_X(w) = sup_{x∈X} {x⊤w}`."

**Formalization Note** The supremum is taken in `EReal`; the support function of the empty set is
`−∞`. -/
noncomputable def supportFn {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : Set X) (w : X) : EReal :=
  ⨆ x ∈ S, ((⟪x, w⟫_ℝ : ℝ) : EReal)

end PWDB


