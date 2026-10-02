-- Prove2me | Definitions.Def_HunterPDE_Harmonic_Subharmonic
-- name    : HunterPDE_Harmonic_Subharmonic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:58:40.448202+00:00
-- url     : https://prove2.me/theorems/d59c2fd0-b6d8-4e06-a54e-b9a8100deea9
-- title:
--   Definition 2.4 — subharmonic and superharmonic functions
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be an open set. A function $u \in C^2(\Omega)$ is **subharmonic** if $\Delta u \ge 0$ in $\Omega$, and **superharmonic** if $\Delta u \le 0$ in $\Omega$, where
--   $$\Delta u = \frac{\partial^2 u}{\partial x_1^2} + \cdots + \frac{\partial^2 u}{\partial x_n^2}.$$
--
--   A function is harmonic if and only if it is both subharmonic and superharmonic. These classes satisfy one-sided mean value inequalities (Theorem 2.5) and the strong maximum principle (Theorem 2.13).
--
--   **Formalization Note.** $u$ is a function on all of $\mathbb{R}^n$ (`EuclideanSpace ℝ (Fin n)`) of which only the restriction to $\Omega$ matters; "$u \in C^2(\Omega)$" is `ContDiffOn ℝ 2 u Ω`, and $\Delta$ is Mathlib's `InnerProductSpace.laplacian` (the trace of the Hessian), which on an open set where $u$ is $C^2$ is the sum of the pure second partials.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 22, Definition 2.4

import Mathlib

open Laplacian

namespace HunterPDE.Harmonic

/-- Definition 2.4 of Hunter, *Notes on PDEs*, p. 22: on an open set `Ω ⊆ ℝⁿ`, a function
`u ∈ C²(Ω)` is subharmonic if `Δu ≥ 0` in `Ω`. -/
def IsSubharmonicOn {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiffOn ℝ 2 u Ω ∧ ∀ x ∈ Ω, 0 ≤ Δ u x

/-- Definition 2.4 of Hunter, *Notes on PDEs*, p. 22: on an open set `Ω ⊆ ℝⁿ`, a function
`u ∈ C²(Ω)` is superharmonic if `Δu ≤ 0` in `Ω`. -/
def IsSuperharmonicOn {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiffOn ℝ 2 u Ω ∧ ∀ x ∈ Ω, Δ u x ≤ 0

end HunterPDE.Harmonic


