-- Prove2me | Definitions.Def_TeschlODE_Shared_IsIntegralCurve
-- name    : TeschlODE_Shared_IsIntegralCurve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T17:12:05.820862+00:00
-- url     : https://prove2.me/theorems/eca85624-cd0a-46aa-8f2d-5140fda81abf
-- title:
--   Integral curve of the autonomous system $\dot x = f(x)$ (6.7) on an open interval
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ and $f : \mathbb{R}^n \to \mathbb{R}^n$. For a set of times $J \subseteq \mathbb{R}$ and a curve $\varphi : \mathbb{R} \to \mathbb{R}^n$ we say that $\varphi$ is an **integral curve** of the autonomous system
--   $$\dot x = f(x) \qquad (6.7)$$
--   **in $M$ on $J$** if $J$ is an open interval (open and order-connected; possibly empty or unbounded), $\varphi(t) \in M$ for every $t \in J$, and $\varphi$ is differentiable at every $t \in J$ with $\dot\varphi(t) = f(\varphi(t))$.
--
--   This is the notion of solution from which the flow $\Phi$ of the Hartman–Grobman theorem is built.
--
--   This one definition serves chunk 08-hartman-grobman (through the flow $\Phi$ of Theorem 9.9, Hartman–Grobman, p. 264) and chunk 10-periodic-orbits (through the flow of Lemma 12.1, p. 316, Corollary 12.3 and Theorem 12.4, p. 317, Corollary 12.5, p. 318, Lemmas 12.6 and 12.7, p. 319); both use it only via the shared flow definition `TeschlODE.Shared.IsMaximalFlow`.
--
--   **Formalization Note.** The state space is `Fin n → ℝ`. $f$ is a total function, but only its values on $M$ are read. Only the values of $\varphi$ on $J$ matter; the derivative is the two-sided `HasDerivAt` since $J$ is open.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2, Eq. (6.7) and the definition of integral curve

import Mathlib

namespace TeschlODE.Shared

/-- Teschl, §6.2, p. 189: an integral curve (solution) of the autonomous system `ẋ = f(x)` (6.7)
in `M`, defined on the time set `J`. `J` is an open interval (open and order-connected, possibly
empty or unbounded), `φ` maps `J` into `M`, and `φ` has derivative `f (φ t)` at every `t ∈ J`.
Only the values of `φ` on `J` matter. -/
def IsIntegralCurve {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (M : Set (Fin n → ℝ)) (J : Set ℝ)
    (φ : ℝ → (Fin n → ℝ)) : Prop :=
  IsOpen J ∧ J.OrdConnected ∧ (∀ t ∈ J, φ t ∈ M) ∧ ∀ t ∈ J, HasDerivAt φ (f (φ t)) t

end TeschlODE.Shared


