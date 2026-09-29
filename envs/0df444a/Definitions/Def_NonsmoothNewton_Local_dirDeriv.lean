-- Prove2me | Definitions.Def_NonsmoothNewton_Local_dirDeriv
-- name    : NonsmoothNewton_Local_dirDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:58:59.994373+00:00
-- url     : https://prove2.me/theorems/cc33f389-1290-47be-9f16-9d0e1db0308e
-- title:
--   One-sided directional derivative $F'(x;h)=\lim_{t\downarrow 0}(F(x+th)-F(x))/t$ (2.4)
-- statement:
--   Let $E$ and $G$ be real normed spaces, $F : E \to G$, and $x, h \in E$. The **classic (one-sided) directional derivative** of $F$ at $x$ in the direction $h$ is
--
--   $$
--   F'(x;h) = \lim_{t \downarrow 0} \frac{F(x+th) - F(x)}{t},
--   $$
--
--   where the limit is taken over $t > 0$ only. This file introduces two objects:
--
--   1. the predicate "the limit exists and equals $d$", i.e. $\frac{F(x+th)-F(x)}{t} \to d$ as $t \downarrow 0$;
--   2. the value $F'(x;h)$ itself, defined as the limit whenever it exists.
--
--   One-sidedness is essential: for $F(y) = |y|$ on $\mathbb R$ one has $F'(0;h) = |h|$, while no two-sided derivative exists at $0$. The directional derivative is the linear-in-$t$ model of $F$ used throughout the local convergence analysis of the nonsmooth Newton method.
--
--   **Formalization Note** The value is Lean's `limUnder` along the filter of right neighbourhoods of $0$; it carries meaning only when the limit exists, and every statement that uses the value carries a hypothesis that guarantees existence. Mathlib's `lineDeriv` is two-sided and is deliberately not used.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 355, Proposition 2.1, Eq. (2.4)

import Mathlib
open Filter Topology

namespace NonsmoothNewton.Local

/-- The one-sided (classic) directional derivative of Qi–Sun (1993), Eq. (2.4), p. 355:
`HasDirDerivAt F x h d` means `d = F'(x; h) = lim_{t ↓ 0} (F (x + t h) - F x) / t`.
The limit is taken over `t > 0` only (it is *not* Mathlib's two-sided `lineDeriv`). -/
def HasDirDerivAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x h : E) (d : G) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (F (x + t • h) - F x)) (𝓝[>] 0) (𝓝 d)

/-- The value `F'(x; h)` of the one-sided directional derivative (2.4), as a `limUnder`.
It is meaningful only when the limit exists (`∃ d, HasDirDerivAt F x h d`); every statement
using it carries a hypothesis guaranteeing that. -/
noncomputable def dirDeriv {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x h : E) : G :=
  limUnder (𝓝[>] (0 : ℝ)) (fun t : ℝ => t⁻¹ • (F (x + t • h) - F x))

end NonsmoothNewton.Local


