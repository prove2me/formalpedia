-- Prove2me | Definitions.Def_TeschlODE_Stability_omegaLimitSet
-- name    : TeschlODE_Stability_omegaLimitSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T12:24:14.352775+00:00
-- url     : https://prove2.me/theorems/873a41ec-c306-4d48-b6b2-796680ab0220
-- title:
--   The $\omega_\pm$-limit set of a point
-- statement:
--   Let $M \subseteq \mathbb{R}^n$, let $\Phi$ be a flow on $M$ with maximal intervals $I_x$, and let $\sigma \in \{1, -1\}$. The **$\omega_\sigma$-limit set** of $x$ is the set of those points $y \in M$ for which there is a sequence of times $t_k \in I_x$ with $t_k \to \sigma\infty$ and $\Phi(t_k, x) \to y$:
--   $$\omega_\sigma(x) = \{\, y \in M : \exists\, (t_k) \subseteq I_x,\ \sigma t_k \to +\infty,\ \Phi(t_k, x) \to y \,\}.$$
--   $\omega_+(x)$ is the $\omega$-limit set, $\omega_-(x)$ the $\alpha$-limit set in other texts. It is empty unless $x$ is $\sigma$ complete.
--
--   **Formalization Note.** As in the book, a limit point must belong to $M$: a point of $\partial M$ approached by the orbit is not in $\omega_\sigma(x)$. The sign is the real $\sigma = \pm 1$, as for `semiOrbit`. The name avoids Mathlib's `omegaLimit`, which is defined for global flows.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 193, §6.3, definition of the ω±-limit set

import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.3, p. 193: the `ω_σ`-limit set of `x` (`σ = 1` for `ω₊`, `σ = -1` for `ω₋`):
the points `y ∈ M` for which there is a sequence of times `t_k ∈ I x` with `t_k → σ∞` and
`Φ(t_k, x) → y`. -/
def omegaLimitSet {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n))) (σ : ℝ)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | y ∈ M ∧ ∃ t : ℕ → ℝ, (∀ k, t k ∈ I x) ∧
    Filter.Tendsto (fun k => σ * t k) Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun k => Φ (t k) x) Filter.atTop (nhds y)}

end TeschlODE.Stability


