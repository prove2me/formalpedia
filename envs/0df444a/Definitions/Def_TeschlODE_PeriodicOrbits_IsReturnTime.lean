-- Prove2me | Definitions.Def_TeschlODE_PeriodicOrbits_IsReturnTime
-- name    : TeschlODE_PeriodicOrbits_IsReturnTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T03:52:19.670424+00:00
-- url     : https://prove2.me/theorems/fdf470ad-a420-4751-951d-a0095b905f67
-- title:
--   Return time $\tau$ to $\Sigma$ with $\tau(x_0) = T$ — Lemma 6.9, defining the Poincaré map (6.25)
-- statement:
--   Let $\Phi$ be a flow with maximal intervals $I_x$, let $\Sigma = \{x \in U \mid S(x) = 0\}$, $x_0 \in \mathbb{R}^n$ and $T \in \mathbb{R}$. A function $\tau$ is a **$C^k$ return time to $\Sigma$ near $x_0$ with $\tau(x_0) = T$** if there is an open neighborhood $V$ of $x_0$ on which $\tau$ is $C^k$, $\tau(x_0) = T$, and for every $y \in V$
--   $$\tau(y) \in I_y, \qquad \Phi(\tau(y), y) \in \Sigma .$$
--
--   Lemma 6.9 gives such a $\tau$ whenever $\Sigma$ is transversal to $f$ and $\Phi(T, x_0) \in \Sigma$; if $x_0$ is periodic with period $T$ the **Poincaré map** is
--   $$P_\Sigma(y) = \Phi(\tau(y), y) \qquad (6.25),\ (12.9).$$
--
--   **Formalization Note.** Any $\tau$ with these properties is continuous at $x_0$, so by the implicit function theorem (transversality) it coincides near $x_0$ with the $\tau$ of Lemma 6.9; theorems may therefore quantify over every such $\tau$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 197, §6.4, Lemma 6.9 and Eq. (6.25); p. 317, Eq. (12.9)

import Mathlib

namespace TeschlODE.PeriodicOrbits

/-- Teschl, §6.4, Lemma 6.9 and (6.25), p. 197: `τ` is a return time to the section
`Σ = {x ∈ U | S(x) = 0}` near `x₀` with `τ(x₀) = T`, for the flow `Φ` with maximal time intervals
`I`. That is: on some open neighborhood `V` of `x₀` the function `τ` is `Cᵏ`, `τ(x₀) = T`, and for
every `y ∈ V` the time `τ(y)` lies in `I y` and `Φ(τ(y), y) ∈ Σ` (6.24). When `x₀` is periodic with
period `T` the Poincaré map is `P_Σ(y) = Φ(τ(y), y)` (6.25), (12.9). Lemma 6.9 shows such a `τ`
exists whenever `Σ` is transversal and `Φ(T, x₀) ∈ Σ`; by the implicit function theorem it is
unique near `x₀`. -/
def IsReturnTime {n : ℕ} (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (k : ℕ) (U : Set (Fin n → ℝ)) (S : (Fin n → ℝ) → ℝ) (x₀ : Fin n → ℝ) (T : ℝ)
    (τ : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ V : Set (Fin n → ℝ), IsOpen V ∧ x₀ ∈ V ∧ ContDiffOn ℝ k τ V ∧ τ x₀ = T ∧
    ∀ y ∈ V, τ y ∈ I y ∧ Φ (τ y) y ∈ U ∧ S (Φ (τ y) y) = 0

end TeschlODE.PeriodicOrbits


