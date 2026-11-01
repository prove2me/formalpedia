-- Prove2me | Definitions.Def_PWDB_persp
-- name    : PWDB_persp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:37:12.85998+00:00
-- url     : https://prove2.me/theorems/a41a9a66-6f9c-4857-8bff-88d76719ff4e
-- title:
--   Convex perspective $t f(x/t)$
-- statement:
--   For $f : X \to \overline{\mathbb R}$ on a real inner product space, the **convex perspective** is
--   $$
--   t f(x/t) = \begin{cases} t\, f(x/t) & t > 0,\\ \delta^*_{\operatorname{dom}(f^*)}(x) & t = 0,\\ +\infty & t < 0,\end{cases}
--   $$
--   where $\operatorname{dom}(f^*) = \{w \mid f^*(w) < +\infty\}$.
--
--   The value at $t = 0$ is the recession function of $f$ when $f$ is proper, closed and convex; it is not $0$. The perspective of a conjugate, $\lambda f^*(w/\lambda)$, is the term of the dual problem (D).
--
--   **Formalization Note** The paper defines the perspective on $X \times \mathbb R_+$; the value $+\infty$ for $t < 0$ only places negative multipliers outside the domain. The domain is the published `AubinLipschitz.effDom`.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Definition A.2, p.39

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PWDB_conj
import Definitions.Def_PWDB_supportFn

namespace PWDB

/-- **Convex perspective** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Definition A.2, p.39):
"The convex perspective of a proper, closed and convex function `f : ℝ^{dx} → R̄` is the function
`f̄ : ℝ^{dx} × ℝ₊ → R̄` defined through `f̄(x, t) = t f(x/t)` if `t > 0` and
`f̄(x, 0) = δ∗_{dom(f∗)}(x)`." The paper writes `t f(x/t)` for `f̄(x, t)`, also at `t = 0`.

`persp g u t` is `t · g(u/t)` for `t > 0`, the support function of `dom(g∗)` at `u` for `t = 0`,
and `+∞` for `t < 0`.

**Formalization Note** Values in `EReal`; `dom` is the published `AubinLipschitz.effDom`
(`{x | g x ≠ ⊤}`). The paper's perspective is defined on `ℝ^{dx} × ℝ₊`; the value `+∞` for `t < 0`
extends it so that a negative multiplier is outside the domain, which changes no value at `t ≥ 0`
(every use in the paper has `t ≥ 0`). The branch at `t = 0` is the one the paper prescribes, not
`0 · g(u/0)` (which `EReal` arithmetic would make `0`). The definition is made for every `g`; the
paper's statements apply it to proper, closed, convex functions. -/
noncomputable def persp {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (g : X → EReal) (u : X) (t : ℝ) : EReal :=
  if 0 < t then (t : EReal) * g (t⁻¹ • u)
  else if t = 0 then supportFn (AubinLipschitz.effDom (conj g)) u
  else ⊤

end PWDB


