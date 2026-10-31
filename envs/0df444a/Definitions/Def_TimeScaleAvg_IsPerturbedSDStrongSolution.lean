-- Prove2me | Definitions.Def_TimeScaleAvg_IsPerturbedSDStrongSolution
-- name    : TimeScaleAvg_IsPerturbedSDStrongSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:02.852088+00:00
-- url     : https://prove2.me/theorems/dc90c59f-00b4-4874-b136-2dcbe47e59ea
-- title:
--   Strong solution of the perturbed steepest descent (6)
-- statement:
--   Let $f:\mathcal H\to\mathbb R$, $g:[t_0,+\infty[\to\mathcal H$. A trajectory $z$ with velocity $\dot z$ is a (strong) solution of the perturbed steepest descent on $[t_0,+\infty[$ when $\dot z$ is integrable on every bounded interval $[t_0,T]$, $z(t)=z(t_0)+\int_{t_0}^{t}\dot z(u)\,du$ for every $t\ge t_0$, and
--
--   $$
--   \dot z(t)+\nabla f(z(t))=g(t)\qquad\text{for almost every }t\ge t_0.
--   $$
--
--   **Formalization Note** Theorem 1 allows any $g$ satisfying (7), not necessarily continuous, so the solution is taken in the strong sense ($z$ locally absolutely continuous, equation almost everywhere). Every classical solution with $g$ satisfying (7) is a strong solution. Trajectories are maps $\mathbb R\to\mathcal H$ constrained on the half-line only.
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eq. (6), Theorem 1, p.3

import Mathlib

open MeasureTheory

namespace TimeScaleAvg

/-- `z`, with velocity `zdot`, is a (strong) solution trajectory on `[t₀, +∞[` of the perturbed
steepest descent (6), `ż(t) + ∇f(z(t)) = g(t)` (Attouch, Boţ & Nguyen, arXiv:2208.08260v3,
Theorem 1, p.3).

**Formalization Note.** Theorem 1 allows any `g` with `∫ ‖g‖ < +∞` and `∫ t ‖g‖² < +∞` (7), so `g`
need not be continuous, and the solution is understood in the strong sense: `zdot` is integrable on
every bounded interval `[t₀, T]`, `z(t) = z(t₀) + ∫_{t₀}^{t} ż(u) du` for every `t ≥ t₀` (so `z` is
locally absolutely continuous), and (6) holds for almost every `t ≥ t₀`. A classical solution
(differentiable at every `t ≥ t₀` with (6) at every `t ≥ t₀`, `g` satisfying (7)) is a strong
solution. The trajectories are maps `ℝ → H` tied down on the half-line only. The positivity
`0 < t₀` of the time origin (p.2) is a separate hypothesis of each statement. -/
def IsPerturbedSDStrongSolution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (g : ℝ → H) (t₀ : ℝ) (z zdot : ℝ → H) : Prop :=
  (∀ T : ℝ, IntegrableOn zdot (Set.Icc t₀ T)) ∧
    (∀ t ∈ Set.Ici t₀, z t = z t₀ + ∫ u in t₀..t, zdot u) ∧
    ∀ᵐ t ∂(volume.restrict (Set.Ici t₀)), zdot t + gradient f (z t) = g t

end TimeScaleAvg


