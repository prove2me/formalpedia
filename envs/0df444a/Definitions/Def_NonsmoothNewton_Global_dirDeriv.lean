-- Prove2me | Definitions.Def_NonsmoothNewton_Global_dirDeriv
-- name    : NonsmoothNewton_Global_dirDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:06:01.866818+00:00
-- url     : https://prove2.me/theorems/be4cacd7-e66c-4419-a48c-3f5c9e53c824
-- title:
--   One-sided directional derivative $F'(x;h)=\lim_{t\downarrow 0}(F(x+th)-F(x))/t$ (2.4)
-- statement:
--   Let $E$ and $G$ be finite-dimensional real normed spaces and $F : E \to G$. For a point $x \in E$ and a direction $h \in E$, the **classical (one-sided) directional derivative** of $F$ at $x$ in direction $h$ is
--
--   $$
--   F'(x;h) = \lim_{t \downarrow 0} \frac{F(x+th) - F(x)}{t},
--   $$
--
--   whenever this limit exists. This file provides two objects:
--
--   1. the predicate $\mathrm{HasDirDerivAt}(F,x,h,d)$, which says that the limit exists and equals $d$;
--   2. the value $\mathrm{dirDeriv}(F,x,h)$, the limit itself.
--
--   The directional derivative is the first-order model of a nonsmooth map: the Newton-type conditions of Qi and Sun compare $V h$ for $V$ in the generalized Jacobian, and the increment $F(y) - F(x)$, with $F'(x; y-x)$.
--
--   **Formalization Note** The value $\mathrm{dirDeriv}$ is Mathlib's `limUnder` along the filter $t \to 0^+$; it is a genuine directional derivative only when the limit exists, and otherwise returns an unspecified value. Statements in this mission use it only at points where $F$ is semismooth, where the paper's Eq. (2.7) guarantees existence. Mathlib's `lineDeriv` is two-sided and is deliberately not used.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 355, Proposition 2.1, Eq. (2.4)

import Mathlib

namespace NonsmoothNewton.Global

open Filter Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- `HasDirDerivAt F x h d`: the classical one-sided directional derivative of `F` at `x` in
direction `h` exists and equals `d`, i.e. `(F (x + t h) - F x) / t → d` as `t ↓ 0`
(Qi–Sun 1993, p. 355, Eq. (2.4)). -/
def HasDirDerivAt (F : E → G) (x h : E) (d : G) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (F (x + t • h) - F x)) (𝓝[>] 0) (𝓝 d)

/-- `dirDeriv F x h` is the paper's `F'(x; h) = lim_{t ↓ 0} (F (x + t h) - F x) / t`
(Eq. (2.4)), taken as `limUnder` along `t ↓ 0`. It is the true one-sided directional derivative
only when that limit exists; this file uses it only where semismoothness guarantees existence
(Eq. (2.7), p. 355). -/
noncomputable def dirDeriv (F : E → G) (x h : E) : G :=
  limUnder (𝓝[>] (0 : ℝ)) (fun t : ℝ => t⁻¹ • (F (x + t • h) - F x))

end NonsmoothNewton.Global


