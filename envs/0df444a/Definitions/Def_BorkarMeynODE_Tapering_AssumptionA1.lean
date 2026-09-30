-- Prove2me | Definitions.Def_BorkarMeynODE_Tapering_AssumptionA1
-- name    : BorkarMeynODE_Tapering_AssumptionA1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:37:57.507201+00:00
-- url     : https://prove2.me/theorems/f7d77493-87c4-433e-be85-a38b8e49f5d9
-- title:
--   Scaled vector field $h_r(x)=h(rx)/r$ and assumption (A1)
-- statement:
--   Let $h:\mathbb R^d\to\mathbb R^d$. For $r>0$ the **scaled vector field** is
--   $$
--   h_r(x) = \frac{h(rx)}{r}, \qquad x\in\mathbb R^d ,
--   $$
--   and the associated scaled ODE is $\dot x(t) = h_r(x(t))$, $t\ge0$ (equations (1.3)–(1.4) of the paper).
--
--   Given a second map $h_\infty:\mathbb R^d\to\mathbb R^d$, **assumption (A1)** for the pair $(h,h_\infty)$ states:
--
--   1. $h$ is Lipschitz;
--   2. $h_r(x)\to h_\infty(x)$ as $r\to\infty$, for every $x\in\mathbb R^d$;
--   3. the origin is an asymptotically stable equilibrium of the **fluid-limit ODE** $\dot x(t) = h_\infty(x(t))$ (equation (1.5)).
--
--   Assumption (A1) is the paper's standing condition on the drift: it says that the "large-state" dynamics of the recursion, seen after rescaling space by the size of the state, are driven towards the origin. It is imposed throughout Sections 2 and 4.
--
--   **Formalization Note** `scaledField h r x = r⁻¹ • h (r • x)`; the paper only uses it for $r>0$. The limit function $h_\infty$ is a parameter; since limits are unique, (A1) determines it. No Lipschitz hypothesis is placed on $h_\infty$: it follows from item 1 (the paper notes this on p. 460). The stability notion is the one of the definition file `ODEStability`.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 448, Eqs. (1.3)-(1.5); p. 449, Assumption (A1)

import Mathlib
import Definitions.Def_BorkarMeynODE_Tapering_ODEStability

namespace BorkarMeynODE.Tapering

open Filter Topology

/-- The scaled vector field `h_r(x) = h(r x)/r` of (1.3). The paper uses it for `r > 0`
(in the proofs, `r ≥ 1`). -/
noncomputable def scaledField {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (r : ℝ) : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  fun x => r⁻¹ • h (r • x)

/-- Assumption (A1) of Borkar–Meyn (p. 449) for the pair `(h, hInf)`: `h` is Lipschitz,
`h_r(x) → hInf(x)` as `r → ∞` for every `x` (so `hInf` is the function `h_∞` whose existence
(A1) asserts; it is determined by the limit), and the origin is an asymptotically stable
equilibrium of the fluid-limit ODE (1.5) `ẋ = h_∞(x)`. No Lipschitz hypothesis is placed on
`hInf`: it follows from the Lipschitz property of `h` (p. 460). -/
def AssumptionA1 {d : ℕ} (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  (∃ K : NNReal, LipschitzWith K h) ∧
    (∀ x : EuclideanSpace ℝ (Fin d),
      Tendsto (fun r : ℝ => scaledField h r x) atTop (𝓝 (hInf x))) ∧
    IsAsymptoticallyStable hInf 0

end BorkarMeynODE.Tapering


