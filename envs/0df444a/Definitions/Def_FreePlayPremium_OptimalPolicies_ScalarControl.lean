-- Prove2me | Definitions.Def_FreePlayPremium_OptimalPolicies_ScalarControl
-- name    : FreePlayPremium_OptimalPolicies_ScalarControl
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:27:13.174703+00:00
-- url     : https://prove2.me/theorems/c41dfa9f-80fb-48e4-a5f2-1f1ff43aab9c
-- title:
--   Scalar continuous-time controlled trajectories
-- statement:
--   A scalar control system consists of a real horizon $T$, initial state $x_0$, state domain $X\subseteq\mathbb R$, control domain $U\subseteq\mathbb R^2$, and drift $f:\mathbb R\times\mathbb R^2\to\mathbb R$. A path consists of a control $u(t)$ and state $x(t)$. It is admissible when $u$ is measurable for completed Lebesgue measure on $[0,T]$, the control and state lie in their domains at every time, the evaluated drift is integrable, and
--   $$x(t)=x_0+\int_{[0,t]}f(x(s),u(s))\,ds\qquad(0\le t\le T).$$
--   This integral equation supplies absolute continuity and the state equation almost everywhere. Two representatives are equivalent when their controls agree almost everywhere on $[0,T]$ and their states agree everywhere there. This generic object imposes neither bounds on the controls nor a policy shape nor an optimality condition. The paper instantiates its two controls as advertising and price.
-- source:
--   Mai and Hu (2022), Optimizing Free-to-Play Multiplayer Games with Premium Subscription, Management Science, https://doi.org/10.1287/mnsc.2022.4510, Problem (3), printed pp. 13–14 (PDF pp. 13–14), continuous-time integral-trajectory convention

import Mathlib

open MeasureTheory Set

namespace FreePlayPremium.OptimalPolicies

/-- A scalar state driven by two real controls, with arbitrary admissible domains. -/
structure ScalarControlSystem where
  horizon : ℝ
  initial : ℝ
  states : Set ℝ
  controls : Set (ℝ × ℝ)
  drift : ℝ → (ℝ × ℝ) → ℝ

/-- A representative of a control and its state trajectory. -/
structure ControlPath where
  control : ℝ → ℝ × ℝ
  state : ℝ → ℝ

/-- Integral trajectories: integrable drift makes the state absolutely continuous.
Controls need only be measurable for completed Lebesgue measure on the horizon. -/
def ScalarControlSystem.Admissible (M : ScalarControlSystem) (q : ControlPath) : Prop :=
  AEMeasurable q.control (volume.restrict (Icc 0 M.horizon)) ∧
  (∀ t ∈ Icc 0 M.horizon, q.control t ∈ M.controls ∧ q.state t ∈ M.states) ∧
  IntegrableOn (fun t => M.drift (q.state t) (q.control t)) (Icc 0 M.horizon) ∧
  (∀ t ∈ Icc 0 M.horizon,
    q.state t = M.initial + ∫ s in Icc 0 t, M.drift (q.state s) (q.control s))

/-- Optimization identifies controls almost everywhere; states use their continuous representatives. -/
def ControlPath.Equivalent (T : ℝ) (q z : ControlPath) : Prop :=
  q.control =ᵐ[volume.restrict (Icc 0 T)] z.control ∧
  ∀ t ∈ Icc 0 T, q.state t = z.state t

end FreePlayPremium.OptimalPolicies


