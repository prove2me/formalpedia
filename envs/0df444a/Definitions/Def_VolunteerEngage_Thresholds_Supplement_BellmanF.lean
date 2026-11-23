-- Prove2me | Definitions.Def_VolunteerEngage_Thresholds_Supplement_BellmanF
-- name    : VolunteerEngage_Thresholds_Supplement_BellmanF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:06:52.702954+00:00
-- url     : https://prove2.me/theorems/fa00e8f1-b1e3-4891-af7a-add2a216163c
-- title:
--   The Bellman equation (59)–(60), with an attained minimum
-- statement:
--   For the published model $M$, a positive constant $\beta$ and real functions $f,f',f''$, the original Bellman problem requires $f$ to be twice continuously differentiable on $[0,\infty)$ and
--
--   $$\beta=\min_{x\in[\theta_0,\theta_L]}\left\{\frac{\sigma^2}{2}f''(w)+(x-\kappa w)f'(w)+c(x)\right\},\qquad w\ge0,$$
--
--   with $f'(0)=-p$, $f'$ strictly increasing and $f'(w)\to0$. This is the equation used in the verification of policy optimality.
--
--   **Formalization Note** First and second derivatives are explicit functions, with derivatives within the half-line at zero and continuous second derivative there. `IsLeast` asserts both equality to the minimum and attainment; no minimizer is assumed as a premise.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, p. 20, (59)–(60)

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Setting

namespace VolunteerEngage.Thresholds.Supplement

open Filter Topology

/-- (59)–(60), with explicit first and second derivatives, one-sided at zero.
`IsLeast` includes attainment of the displayed minimum. -/
def IsFBellmanSol (M : Model) (β : ℝ) (f f' f'' : ℝ → ℝ) : Prop :=
  0 < β ∧ ContinuousOn f'' (Set.Ici 0) ∧
  (∀ w ∈ Set.Ici (0 : ℝ), HasDerivWithinAt f (f' w) (Set.Ici 0) w) ∧
  (∀ w ∈ Set.Ici (0 : ℝ), HasDerivWithinAt f' (f'' w) (Set.Ici 0) w) ∧
  (∀ w : ℝ, 0 ≤ w → IsLeast
    ((fun x => M.σ ^ 2 / 2 * f'' w + (x - M.κ * w) * f' w + cost M x) ''
      Set.Icc M.θ0 (M.θ M.L)) β) ∧
  f' 0 = -M.p ∧ StrictMonoOn f' (Set.Ici 0) ∧ Tendsto f' atTop (𝓝 0)

end VolunteerEngage.Thresholds.Supplement


