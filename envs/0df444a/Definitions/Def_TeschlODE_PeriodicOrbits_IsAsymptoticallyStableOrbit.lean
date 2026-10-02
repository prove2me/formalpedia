-- Prove2me | Definitions.Def_TeschlODE_PeriodicOrbits_IsAsymptoticallyStableOrbit
-- name    : TeschlODE_PeriodicOrbits_IsAsymptoticallyStableOrbit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T04:46:58.711278+00:00
-- url     : https://prove2.me/theorems/18b2c7cf-5001-4740-86de-02d7adfa8a19
-- title:
--   Asymptotically stable orbit (12.1)
-- statement:
--   An orbit $\gamma$ of the flow $\Phi$ on $M$ is **asymptotically stable** if it is stable and there is a neighborhood $U \subseteq M$ of $\gamma$ such that for every $x \in U$ the solution exists for all $t \ge 0$ and
--   $$\lim_{t \to \infty} d\big(\Phi(t, x), \gamma\big) = 0, \qquad d(x, A) = \inf\{|x - y| \mid y \in A\}. \qquad (12.1)$$
--
--   **Formalization Note.** The book writes "for all $x \in U(x_0)$" right after introducing the neighborhood $U(\gamma(x_0))$ of the orbit; the latter is taken (a neighborhood of a single point would be a different, weaker condition). $d$ is `Metric.infDist`; the state space `Fin n → ℝ` carries the sup norm, which gives the same limit condition as the Euclidean norm.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 315, §12.1, Eq. (12.1)

import Mathlib
import Definitions.Def_TeschlODE_PeriodicOrbits_IsStableOrbit

namespace TeschlODE.PeriodicOrbits

/-- Teschl, §12.1, p. 315, (12.1): the orbit `γ` is asymptotically stable: it is stable and there
is a neighborhood `U ⊆ M` of `γ` such that for every `x ∈ U` the solution exists for all `t ≥ 0`
and `d(Φ(t, x), γ) → 0` as `t → ∞`, where `d(x, A) = inf {|x − y| | y ∈ A}`. (The book writes
"for all `x ∈ U(x₀)`" for the neighborhood `U(γ(x₀))` it has just introduced; the latter is
taken.) -/
def IsAsymptoticallyStableOrbit {n : ℕ} (M : Set (Fin n → ℝ)) (I : (Fin n → ℝ) → Set ℝ)
    (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (γ : Set (Fin n → ℝ)) : Prop :=
  IsStableOrbit M I Φ γ ∧
  ∃ U ∈ nhdsSet γ, U ⊆ M ∧ ∀ x ∈ U, (∀ t : ℝ, 0 ≤ t → t ∈ I x) ∧
    Filter.Tendsto (fun t => Metric.infDist (Φ t x) γ) Filter.atTop (nhds 0)

end TeschlODE.PeriodicOrbits


