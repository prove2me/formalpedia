-- Prove2me | Definitions.Def_FracMPGA_proxSet
-- name    : FracMPGA_proxSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:10.312653+00:00
-- url     : https://prove2.me/theorems/597cf05d-b15d-4945-8cfe-b1ed76ea614c
-- title:
--   Proximity operator $\operatorname{prox}_{\alpha\varphi}$ as an argmin set
-- statement:
--   For $\alpha>0$ and a function $\varphi:V\to(-\infty,+\infty]$ on a normed space $V$, the **proximity operator** of $\alpha\varphi$ at $v$ is the set of minimizers
--   $$
--   \operatorname{prox}_{\alpha\varphi}(v)=\operatorname*{arg\,min}\Big\{\alpha\varphi(z)+\tfrac12\|z-v\|_2^2:\ z\in V\Big\}.
--   $$
--   It may contain several points when $\varphi$ is nonconvex, and it is a single point when $\varphi$ is proper, closed and convex.
--
--   The multi-proximity gradient algorithm takes proximity steps of the conjugate $g^*$ in $y$ and of the block functions $f_i$ in $x$.
--
--   **Formalization Note** The objective is computed in extended reals, so a point where $\varphi=+\infty$ is never a minimizer unless $\varphi\equiv+\infty$. Writing "$p=\operatorname{prox}_{\alpha\varphi}(v)$" is rendered as membership in this set.
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §4, p.13 (definition of the proximity operator)

import Mathlib

namespace FracMPGA

/-- The **proximity operator** of Zhou, Zhang, Li, *An equivalent reformulation and
multi-proximity gradient algorithms for a class of nonsmooth fractional programming*,
arXiv:2311.00957v2, §4, p.13: for `α > 0` and `φ : V → (−∞, +∞]`,
`prox_{αφ}(v) := argmin { α φ(z) + ½ ‖z − v‖₂² : z ∈ V }`.

`proxSet α φ v` is the whole argmin **set** (the paper's prox may be set-valued when `φ` is
nonconvex, p.13); "`p = prox_{αφ}(v)`" and "`p ∈ prox_{αφ}(v)`" are both written `p ∈ proxSet α φ v`.

**Formalization Note** The objective is computed in `EReal`, with `α φ(z)` as the product
`(α : EReal) * φ z`, so a point with `φ z = +∞` is never a minimizer unless every point has
`φ = +∞`. Properness and lower semicontinuity of `φ`, under which the paper defines the operator,
are not part of the definition; they are hypotheses of the statements that use it. -/
def proxSet {V : Type*} [NormedAddCommGroup V] (α : ℝ) (φ : V → EReal) (v : V) : Set V :=
  {p | ∀ z : V, (α : EReal) * φ p + ((‖p - v‖ ^ 2 / 2 : ℝ) : EReal) ≤
    (α : EReal) * φ z + ((‖z - v‖ ^ 2 / 2 : ℝ) : EReal)}

end FracMPGA


