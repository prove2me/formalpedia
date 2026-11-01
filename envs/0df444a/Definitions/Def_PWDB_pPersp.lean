-- Prove2me | Definitions.Def_PWDB_pPersp
-- name    : PWDB_pPersp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:37:13.72543+00:00
-- url     : https://prove2.me/theorems/2bed6ab2-587a-4717-a732-654042ce3d05
-- title:
--   Convex partial perspective $t f(x/t, z)$
-- statement:
--   For $g : E \times F \to \overline{\mathbb R}$ the **convex partial perspective** is
--   $$
--   t g(x/t, z) = \begin{cases} t\, g(x/t, z) & t > 0,\\ \delta^*_{\operatorname{dom}(g^{*1}(\cdot, z))}(x) & t = 0,\\ +\infty & t < 0.\end{cases}
--   $$
--   In the dual best problem it is applied to $g = f_i^{*1}$: for a real-valued $f_i$ the value at $\lambda_i = 0$ is $0$ if $w_i = 0$ and $+\infty$ otherwise.
--
--   **Formalization Note** The paper defines it for $t \in \mathbb R_+$; $+\infty$ for $t < 0$ places negative multipliers outside the domain.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Definition A.4, p.41

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PWDB_PartialConj
import Definitions.Def_PWDB_supportFn

namespace PWDB

/-- **Convex partial perspective** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Definition A.4,
p.41): "If `f : ℝ^{dx} × ℝ^{dz} → R̄` is proper, closed and convex in its first argument, then we
define its convex partial perspective `f̄ : ℝ^{dx} × ℝ₊ × ℝ^{dz} → R̄` through
`f̄(x, t, z) = t f(x/t, z)` if `t > 0` and `f̄(x, 0, z) = δ∗_{dom(f∗1(·,z))}(x)`." The paper writes
`t f(x/t, z)` for `f̄(x, t, z)`, also at `t = 0`.

`pPersp g x t z` is `t · g(x/t, z)` for `t > 0`, the support function of `dom(g∗1(·, z))` at `x`
for `t = 0`, and `+∞` for `t < 0`.

**Formalization Note** Values in `EReal`; `dom` is `AubinLipschitz.effDom`. The paper defines the
partial perspective on `t ∈ ℝ₊`; the value `+∞` for `t < 0` places negative multipliers outside the
domain and changes no value at `t ≥ 0`. In (D-B) the paper applies it to `g = fi∗1`, i.e.
`pPersp (pconj1 f) w λ z` is `λ fi∗1(w/λ, z)`. -/
noncomputable def pPersp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → F → EReal) (x : E) (t : ℝ) (z : F) : EReal :=
  if 0 < t then (t : EReal) * g (t⁻¹ • x) z
  else if t = 0 then supportFn (AubinLipschitz.effDom (fun w => pconj1 g w z)) x
  else ⊤

end PWDB


