-- Prove2me | Definitions.Def_TeschlODE_LocalBehavior_IsNorm
-- name    : TeschlODE_LocalBehavior_IsNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T17:08:03.102957+00:00
-- url     : https://prove2.me/theorems/b36c0537-d476-4a81-a821-6c9b5c368576
-- title:
--   A norm on $\mathbb{R}^n$ given as a function
-- statement:
--   A function $N : \mathbb{R}^n \to \mathbb{R}$ is a **norm** if for all $x, y \in \mathbb{R}^n$ and $c \in \mathbb{R}$
--   $$N(x) = 0 \iff x = 0, \qquad N(x + y) \le N(x) + N(y), \qquad N(c x) = |c|\, N(x).$$
--   Nonnegativity follows from these three axioms.
--
--   Lemma 9.7 is stated in a norm "chosen" so that the contracting and expanding parts of a hyperbolic matrix are strict contractions; this is in general not the Euclidean norm, so the norm is an explicit parameter of that statement.
--
--   **Formalization Note.** `Fin n → ℝ` already carries the sup norm as an instance; a second norm is passed as a plain function with these axioms rather than as a competing instance.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 262, §9.3 ("choose a norm such that …", Lemma 9.7; cf. Problem 3.48)

import Mathlib

namespace TeschlODE.LocalBehavior

/-- A norm on `ℝⁿ` given as a function `N`: definite, subadditive and absolutely homogeneous
(nonnegativity follows). Teschl, §9.3, p. 262, Lemma 9.7 "choose a norm such that …": the
lemma is stated for a norm on `ℝⁿ` other than the Euclidean one, so the norm is a parameter. -/
def IsNorm {n : ℕ} (N : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ x, N x = 0 ↔ x = 0) ∧ (∀ x y, N (x + y) ≤ N x + N y) ∧ ∀ (c : ℝ) x, N (c • x) = |c| * N x

end TeschlODE.LocalBehavior


