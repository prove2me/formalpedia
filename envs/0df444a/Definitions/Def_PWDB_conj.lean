-- Prove2me | Definitions.Def_PWDB_conj
-- name    : PWDB_conj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:14.905973+00:00
-- url     : https://prove2.me/theorems/5eb01394-589e-443c-8e9a-8701372fa11b
-- title:
--   Conjugate function $f^*$
-- statement:
--   Let $X$ be a real inner product space. The **conjugate** of $f : X \to \overline{\mathbb R}$ is
--   $$
--   f^*(w) = \sup_{x \in X} \{\langle x, w\rangle - f(x)\}, \qquad w \in X .
--   $$
--   The conjugate of $f^*$ is the biconjugate $f^{**}$.
--
--   **Formalization Note** The supremum is taken in `EReal` over the whole space; points with $f(x) = +\infty$ contribute $-\infty$.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Definition A.1, p.39

import Mathlib

open scoped InnerProductSpace

namespace PWDB

/-- **Conjugate function** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Definition A.1, p.39):
"The conjugate of a function `f : ℝ^{dx} → R̄` is the function `f∗ : ℝ^{dx} → R̄` defined through
`f∗(w) = sup_x {x⊤w − f(x)}`."

**Formalization Note** The supremum is taken in `EReal` over the whole space, so points with
`f(x) = +∞` contribute `−∞` and points with `f(x) = −∞` contribute `+∞`. The space is a real inner
product space `X` (the paper's is `ℝ^{dx}`), identified with its dual through the inner product. -/
noncomputable def conj {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (g : X → EReal) (w : X) : EReal :=
  ⨆ x : X, ((⟪x, w⟫_ℝ : ℝ) : EReal) - g x

end PWDB


