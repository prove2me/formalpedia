-- Prove2me | Definitions.Def_TeschlODE_Planar_omegaLimitSet
-- name    : TeschlODE_Planar_omegaLimitSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T14:52:24.470849+00:00
-- url     : https://prove2.me/theorems/ff2e814e-2ada-43db-af90-9f7ea6d7f022
-- title:
--   The ω±-limit set of a point
-- statement:
--   The **$\omega_\sigma$-limit set** of $x \in M$ ($\sigma \in \{+,-\}$) is the set of points $y \in M$ for which there is a sequence of times $t_k \in I_x$ with $t_k \to \sigma\infty$ and
--   $$\Phi(t_k, x) \to y .$$
--
--   It is a closed invariant set (Lemma 6.5), empty unless $x$ is $\sigma$ complete, and depends only on the orbit of $x$. The Poincaré–Bendixson theory of the plane classifies these sets.
--
--   **Formalization Note.** $\sigma$ is a `Bool` (`true` = $+$, filter `atTop`; `false` = $-$, filter `atBot`). Limit points are required to lie in $M$, as in the book ("those points $y \in M$"); a limit on $\partial M$ does not count.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 193, §6.3

import Mathlib
import Definitions.Def_TeschlODE_Planar_flow

namespace TeschlODE.Planar

open Filter Topology

/-- Teschl, §6.3, p. 193: the `ω_σ`-limit set of `x` (`σ = true` is the book's `ω₊`,
`σ = false` its `ω₋`): the set of points `y ∈ M` for which there is a sequence of times
`t_k ∈ I_x` with `t_k → σ∞` and `Φ(t_k, x) → y`. It is empty unless `x` is `σ` complete, and
empty when `x ∉ M`. -/
def omegaLimitSet {n : ℕ} (f : (Fin n → ℝ) → Fin n → ℝ) (M : Set (Fin n → ℝ)) (σ : Bool)
    (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | y ∈ M ∧ ∃ u : ℕ → ℝ, (∀ k, u k ∈ lifetime f M x) ∧
    Tendsto u atTop (if σ then atTop else atBot) ∧
    Tendsto (fun k => flow f M (u k) x) atTop (𝓝 y)}

end TeschlODE.Planar


