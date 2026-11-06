-- Prove2me | Definitions.Def_DelayedGamesMAO_IsGradientOn
-- name    : DelayedGamesMAO_IsGradientOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:41.413+00:00
-- url     : https://prove2.me/theorems/97777bf0-1639-49af-b5f4-390771c4fa9c
-- title:
--   $d\psi$ is a derivative of $\psi$ within $W$
-- statement:
--   Let $W$ be a subset of a real normed space $E$, $\psi:E\to\mathbb R$, and $d\psi$ a map from $E$ to the dual space $E^*$. The predicate says that for every $w\in W$, $d\psi(w)$ is a Fréchet derivative of $\psi$ at $w$ within $W$:
--   $$
--   \psi(v)=\psi(w)+d\psi(w)(v-w)+o(\|v-w\|)\qquad(v\to w,\ v\in W).
--   $$
--   This is how "$\psi$ is differentiable on $W$ with gradient $\nabla\psi$" is expressed throughout the mission.
--
--   **Formalization Note** The gradient is an explicit field. Nothing is asked of $\psi$ off $W$, and the notion stays meaningful when $W$ has empty interior (a simplex), where Lean's `fderivWithin` would be the junk value $0$. Values of $d\psi$ off $W$ are never used.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2–3, pp.3–5 (differentiable regularizer and losses)

import Mathlib

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **`dψ` is a derivative of `ψ` within `W`** at every point of `W`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 and §3, pp.3–5: the regularizer `ψ : W → ℝ` and the losses are "differentiable"
functions on the domain `W`, with gradient `∇ψ`.

**Formalization Note.** The gradient is an explicit field `dψ : E → (E →L[ℝ] ℝ)` (a dual vector),
required to be a Fréchet derivative of `ψ` within `W` at every `w ∈ W`. This asks nothing of
`ψ` off `W` (unlike `fderiv`), and it is meaningful when `W` has empty interior (a simplex),
where `fderivWithin` would be the junk value `0`. Values of `dψ` off `W` are never used. -/
def IsGradientOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Set E)
    (ψ : E → ℝ) (dψ : E → E →L[ℝ] ℝ) : Prop :=
  ∀ w ∈ W, HasFDerivWithinAt ψ (dψ w) W w

end DelayedGamesMAO


