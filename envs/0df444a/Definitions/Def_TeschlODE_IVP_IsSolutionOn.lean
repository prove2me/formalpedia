-- Prove2me | Definitions.Def_TeschlODE_IVP_IsSolutionOn
-- name    : TeschlODE_IVP_IsSolutionOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:49:49.222415+00:00
-- url     : https://prove2.me/theorems/ab1db2f6-0780-40d9-934c-c4d08e444b23
-- title:
--   Solution of the initial value problem (2.10) on an interval, with graph in U
-- statement:
--   Let $n \in \mathbb{N}$, let $U \subseteq \mathbb{R} \times \mathbb{R}^n$, let $f : \mathbb{R} \times \mathbb{R}^n \to \mathbb{R}^n$ and let $I \subseteq \mathbb{R}$ be a set of times (an interval in every use). A function $x : \mathbb{R} \to \mathbb{R}^n$ is a **solution of**
--   $$\dot x = f(t, x) \qquad (2.10)$$
--   **on $I$ with graph in $U$** if for every $t \in I$ the point $(t, x(t))$ lies in $U$ and $x$ is differentiable at $t$ relative to $I$ with derivative $f(t, x(t))$.
--
--   The initial condition $x(t_0) = x_0$ of (2.10) is stated separately in every theorem that uses this notion. When $f$ is continuous on $U$, the derivative $t \mapsto f(t, x(t))$ is continuous on $I$, so a solution in this sense is a $C^1$ function on $I$, as in the book.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`, so $|x|$ is the Euclidean norm (2.2). The book's $f$ is defined on an open set $U \subseteq \mathbb{R}^{n+1}$; here it is a total function on $\mathbb{R} \times \mathbb{R}^n$ and only its values on $U$ enter (the graph of a solution stays in $U$). The derivative is `HasDerivWithinAt … I t`, which is the one-sided derivative at an endpoint of $I$ that belongs to $I$; only the values of $x$ on $I$ matter.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 36, §2.2, Eq. (2.10)

import Mathlib

namespace TeschlODE.IVP

/-- Teschl, §2.2, (2.10): `x` solves `ẋ = f(t, x)` on the set `I` (in practice an interval)
with graph in `U`: for every `t ∈ I` the point `(t, x t)` lies in `U` and `x` has derivative
`f (t, x t)` at `t` relative to `I` (one-sided at an endpoint of `I` that belongs to `I`). -/
def IsSolutionOn {n : ℕ} (U : Set (ℝ × EuclideanSpace ℝ (Fin n)))
    (f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (I : Set ℝ) (x : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ t ∈ I, (t, x t) ∈ U ∧ HasDerivWithinAt x (f (t, x t)) I t

end TeschlODE.IVP


