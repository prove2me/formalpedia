-- Prove2me | Definitions.Def_DelayedGamesMAO_Assumption2
-- name    : DelayedGamesMAO_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:48.929273+00:00
-- url     : https://prove2.me/theorems/8ecc9225-1e55-49e3-84aa-b9728a54d4e0
-- title:
--   Assumption 2 — strongly convex regularizer, bounded Bregman radius
-- statement:
--   Let $W$ be a subset of a finite-dimensional real normed space. A regularizer $\psi$ with gradient field $d\psi$, a reference point $w_0$ and a constant $M$ satisfy **Assumption 2** if
--
--   1. $\psi$ is differentiable on $W$ with gradient $d\psi$;
--   2. $\psi$ is 1-strongly convex with respect to $\|\cdot\|$: $D_\psi(u\mid w)\ge\frac12\|u-w\|^2$ for all $u,w\in W$;
--   3. $M>0$, $w_0\in W$, and $D_\psi(w\mid w_0)\le M$ for all $w\in W$.
--
--   The constant $M$ (the Bregman radius of $W$ around $w_0$) is known to the learner and enters the optimism weight $\gamma=\max\{4L,2G/\sqrt M\}$.
--
--   **Formalization Note** Differentiability is the gradient field of `IsGradientOn` and $D_\psi$ is `TimeVaryingGames.bregman ψ dψ`.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §3, Assumption 2, p.5

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF
import Definitions.Def_DelayedGamesMAO_IsGradientOn
import Definitions.Def_DelayedGamesMAO_IsOneStronglyConvex

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Assumption 2** (strongly convex regularizer and bounded Bregman radius).
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §3, Assumption 2, p.5: "The regularizer `ψ` is differentiable and 1-strongly convex with
respect to `‖·‖`, i.e., `D_ψ(u | w) ≥ ½‖u − w‖²` for all `u, w ∈ W`. Additionally, there is a
known constant `M > 0` and reference point `w_0 ∈ W` such that `D_ψ(w | w_0) ≤ M` for all
`w ∈ W`."

**Formalization Note.** "Differentiable" is the gradient field `dψ` of `IsGradientOn` (a
derivative of `ψ` within `W`); `D_ψ` is `TimeVaryingGames.bregman ψ dψ`. -/
def Assumption2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Set E)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) (w0 : E) (M : ℝ) : Prop :=
  IsGradientOn W ψ dψ ∧ IsOneStronglyConvex W ψ dψ ∧ 0 < M ∧ w0 ∈ W ∧
    ∀ w ∈ W, TimeVaryingGames.bregman ψ dψ w w0 ≤ M

end DelayedGamesMAO


