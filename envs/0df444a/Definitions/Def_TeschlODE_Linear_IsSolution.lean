-- Prove2me | Definitions.Def_TeschlODE_Linear_IsSolution
-- name    : TeschlODE_Linear_IsSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:54:04.13452+00:00
-- url     : https://prove2.me/theorems/fbd47834-0373-4383-b6cb-64323a732d90
-- title:
--   Solution of the linear system (3.79) on an interval
-- statement:
--   Let $n \in \mathbb{N}$, let $I \subseteq \mathbb{R}$ be a set of times (an interval in every use) and let $A : \mathbb{R} \to \mathbb{R}^{n\times n}$ be a matrix-valued coefficient function. A function $x : \mathbb{R} \to \mathbb{R}^n$ is a **solution of the linear first-order system**
--   $$\dot x(t) = A(t)\,x(t) \qquad (3.79)$$
--   on $I$ if at every $t \in I$ the function $x$ is differentiable relative to $I$ with derivative $A(t)x(t)$.
--
--   This is the object of Section 3.4 of the book; Theorems 3.9–3.12 are statements about it.
--
--   **Formalization Note.** Vectors are `Fin n → ℝ`, matrices `Matrix (Fin n) (Fin n) ℝ`, and $A(t)x(t)$ is `Matrix.mulVec`. The derivative is `HasDerivWithinAt … I t`, so at an endpoint of $I$ that belongs to $I$ it is the one-sided derivative, and only the values of $x$ on $I$ matter.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 81, §3.4, Eq. (3.79)

import Mathlib

namespace TeschlODE.Linear

/-- Teschl (3.79), p. 81: `x` solves the linear first-order system `ẋ(t) = A(t) x(t)` on the
interval `I`, i.e. at every `t ∈ I` it has derivative (within `I`, so one-sided at an endpoint
that belongs to `I`) equal to `A(t) x(t)`. Only the values of `x` on `I` matter. -/
def IsSolution {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (I : Set ℝ)
    (x : ℝ → Fin n → ℝ) : Prop :=
  ∀ t ∈ I, HasDerivWithinAt x (Matrix.mulVec (A t) (x t)) I t

end TeschlODE.Linear


