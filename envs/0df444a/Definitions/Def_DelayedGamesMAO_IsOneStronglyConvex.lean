-- Prove2me | Definitions.Def_DelayedGamesMAO_IsOneStronglyConvex
-- name    : DelayedGamesMAO_IsOneStronglyConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:53.282044+00:00
-- url     : https://prove2.me/theorems/0cc9a40b-a0d0-401d-887f-2b145eb56da1
-- title:
--   1-strong convexity: $D_\psi(u\mid w)\ge\frac12\|u-w\|^2$ on $W$
-- statement:
--   Let $W$ be a subset of a real normed space, $\psi$ a function with gradient field $d\psi$, and
--   $$
--   D_\psi(u\mid w)=\psi(u)-\psi(w)-\langle\nabla\psi(w),u-w\rangle
--   $$
--   its **Bregman divergence**. $\psi$ is **1-strongly convex** with respect to $\|\cdot\|$ on $W$ if
--   $$
--   D_\psi(u\mid w)\ge\tfrac12\|u-w\|^2\qquad\text{for all }u,w\in W .
--   $$
--
--   **Formalization Note** $D_\psi(u\mid w)$ is the published definition `TimeVaryingGames.bregman ψ dψ u w` $=\psi(u)-\psi(w)-d\psi(w)(u-w)$, where $d\psi$ is the gradient field.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §3, Assumption 2, p.5; Bregman divergence p.4

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **1-strong convexity in Bregman form**: `D_ψ(u | w) ≥ ½‖u − w‖²` for all `u, w ∈ W`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §3, Assumption 2, p.5: "1-strongly convex with respect to `‖·‖`, i.e.,
`D_ψ(u | w) ≥ ½‖u − w‖²` for all `u, w ∈ W`", where (p.4)
`D_ψ(u | w) := ψ(u) − ψ(w) − ⟨∇ψ(w), u − w⟩`.

**Formalization Note.** `D_ψ(u | w)` is the published `TimeVaryingGames.bregman ψ dψ u w
= ψ u − ψ w − dψ w (u − w)`, with the gradient field `dψ`. -/
def IsOneStronglyConvex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Set E)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) : Prop :=
  ∀ u ∈ W, ∀ w ∈ W, (1 / 2 : ℝ) * ‖u - w‖ ^ 2 ≤ TimeVaryingGames.bregman ψ dψ u w

end DelayedGamesMAO


