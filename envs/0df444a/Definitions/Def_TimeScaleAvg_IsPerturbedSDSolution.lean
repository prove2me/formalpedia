-- Prove2me | Definitions.Def_TimeScaleAvg_IsPerturbedSDSolution
-- name    : TimeScaleAvg_IsPerturbedSDSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:51.549504+00:00
-- url     : https://prove2.me/theorems/ca1b8705-9ca9-4b7d-b821-bceea4d59fe1
-- title:
--   Solution of the perturbed steepest descent (6)
-- statement:
--   Let $f:\mathcal H\to\mathbb R$, $g:[t_0,+\infty[\to\mathcal H$. A trajectory $z$ with velocity $\dot z$ is a solution of the perturbed steepest descent on $[t_0,+\infty[$ when $z$ is differentiable at every $t\ge t_0$ (one-sided at $t_0$), with derivative $\dot z(t)$, and
--
--   $$
--   \dot z(t)+\nabla f(z(t))=g(t)\qquad\text{for every }t\ge t_0.
--   $$
--
--   For $g\equiv0$ this is the steepest descent (SD).
--
--   **Formalization Note** The solution is classical. Continuity of $\dot z$ and of $g$ is not required. Trajectories are maps $\mathbb R\to\mathcal H$ constrained on the half-line only.
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eq. (6), Theorem 1, p.3

import Mathlib

namespace TimeScaleAvg

/-- `z`, with velocity `zdot`, is a solution trajectory on `[t₀, +∞[` of the perturbed steepest
descent (6), `ż(t) + ∇f(z(t)) = g(t)` (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, Theorem 1, p.3).

**Formalization Note.** A solution is classical: at every `t ≥ t₀` the map `z` has derivative
`zdot t` within `[t₀, +∞[` (one-sided at `t₀`) and the equation holds there. The trajectories are
maps `ℝ → H` tied down on the half-line only; their values before `t₀` play no role. Continuity of
`zdot` and of `g` is not asked for. The positivity `0 < t₀` of the time origin (p.2) is a separate
hypothesis of each statement. -/
def IsPerturbedSDSolution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (g : ℝ → H) (t₀ : ℝ) (z zdot : ℝ → H) : Prop :=
  ∀ t ∈ Set.Ici t₀,
    HasDerivWithinAt z (zdot t) (Set.Ici t₀) t ∧ zdot t + gradient f (z t) = g t

end TimeScaleAvg


