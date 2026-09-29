-- Prove2me | Definitions.Def_BertsekasCTModel
-- name    : BertsekasCTModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-07T15:46:49.945675+00:00
-- url     : https://prove2.me/theorems/0f206f91-0eb6-4a22-b615-85af7b1ff1fe
-- title:
--   The continuous-time optimal control problem: admissibility, cost, Hamiltonian
-- statement:
--   This module fixes the continuous-time optimal control problem of Bertsekas, Vol. I, Chapter 3, together with the admissibility class, the cost functional and the Hamiltonian.
--
--   **The problem.** Over a fixed horizon $T > 0$, minimize
--
--   $$h\bigl(x(T)\bigr) + \int_0^T g\bigl(x(t), u(t)\bigr)\, dt \qquad \text{subject to} \qquad \dot x(t) = f\bigl(x(t), u(t)\bigr), \quad x(0) = x_0, \quad u(t) \in U,$$
--
--   where the state $x(t)$ lies in $\mathbb{R}^n$, the control $u(t)$ in $\mathbb{R}^m$, and $U \subseteq \mathbb{R}^m$ is the control constraint set.
--
--   **Admissible controls.** A control is admissible on $[t_0, T]$ if it takes values in $U$ and is piecewise continuous there — its image is bounded and it is continuous off a finite set of times. The corresponding state trajectory is continuous on $[t_0, T]$, starts at the prescribed value, and satisfies the system equation off a finite set of times (the switching times of the control).
--
--   **Cost from an arbitrary start.** For a control/state pair on $[t_0, T]$,
--
--   $$J(t_0, u, x) \;=\; h\bigl(x(T)\bigr) + \int_{t_0}^{T} g\bigl(x(t), u(t)\bigr)\, dt .$$
--
--   Parametrizing by the start $(t_0,\xi)$ rather than only by $(0,x_0)$ is what lets the Hamilton–Jacobi–Bellman verification theorem speak about the cost-to-go from every point.
--
--   **The Hamiltonian.** For $x, p \in \mathbb{R}^n$ and $u \in \mathbb{R}^m$,
--
--   $$H(x,u,p) \;=\; g(x,u) + \langle p, f(x,u) \rangle .$$
--
--   The Minimum Principle is stated entirely in terms of $H$: the state and adjoint equations are its partial gradients in $p$ and $x$, and the optimality condition is its pointwise minimization in $u$.
--
--   **Formalization Note** States and controls live in Euclidean spaces; no regularity is imposed on $f$, $g$, $h$ at the level of the model — the theorems that need continuous differentiability assume it explicitly. Requiring the control's image to be bounded (together with continuity off a finite set) makes the cost integrand of an admissible pair genuinely integrable, so the cost cannot silently collapse to the terminal term. Derivatives are two-sided, so at the endpoints the trajectory is constrained slightly beyond $[t_0,T]$; the constraint set $U$ is an arbitrary subset, with no compactness or convexity assumed.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 3.2; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Chapter 3; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 3.3.1

import Mathlib

/-- The continuous-time optimal control problem of Bertsekas, "Dynamic
Programming and Optimal Control", Vol. I, 3rd ed., Section 3.2:
minimize `h(x(T)) + ∫₀ᵀ g(x(t), u(t)) dt` subject to
`ẋ(t) = f(x(t), u(t))` for `t ∈ [0, T]`, `x(0) = x₀`, and `u(t) ∈ U`.
States live in `ℝⁿ` and controls in `ℝᵐ` (as Euclidean spaces). -/
structure BertsekasCTModel (n m : ℕ) where
  T : ℝ
  hT : 0 < T
  U : Set (EuclideanSpace ℝ (Fin m))
  f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)
  g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ
  h : EuclideanSpace ℝ (Fin n) → ℝ
  x0 : EuclideanSpace ℝ (Fin n)

/-- A function is piecewise continuous on a set if its image of the set is
bounded and it is continuous on the set with at most finitely many points
removed.  On a compact interval this captures the classical notion used for
control trajectories in Chapter 3 of Bertsekas, Vol. I, 3rd ed. (finitely many
discontinuities with finite one-sided limits), and the boundedness makes the
cost integral of an admissible pair genuinely integrable. -/
def BertsekasPiecewiseContinuousOn {E : Type} [NormedAddCommGroup E]
    (u : ℝ → E) (s : Set ℝ) : Prop :=
  Bornology.IsBounded (u '' s) ∧ ∃ F : Finset ℝ, ContinuousOn u (s \ (F : Set ℝ))

/-- `BertsekasCTAdmissibleFrom M t₀ ξ u x` says `(u, x)` is an admissible
control/state trajectory pair on `[t₀, T]` starting from state `ξ` at time
`t₀`: the control is piecewise continuous with values in the constraint set
`U`, and the state trajectory is continuous, starts at `ξ`, and satisfies the
system equation `ẋ(t) = f(x(t), u(t))` away from the finitely many
discontinuity points of the control. -/
def BertsekasCTAdmissibleFrom {n m : ℕ} (M : BertsekasCTModel n m)
    (t₀ : ℝ) (ξ : EuclideanSpace ℝ (Fin n))
    (u : ℝ → EuclideanSpace ℝ (Fin m)) (x : ℝ → EuclideanSpace ℝ (Fin n)) :
    Prop :=
  (∀ t ∈ Set.Icc t₀ M.T, u t ∈ M.U) ∧
  BertsekasPiecewiseContinuousOn u (Set.Icc t₀ M.T) ∧
  ContinuousOn x (Set.Icc t₀ M.T) ∧ x t₀ = ξ ∧
  ∃ F : Finset ℝ, ∀ t ∈ Set.Icc t₀ M.T \ (F : Set ℝ),
    HasDerivAt x (M.f (x t) (u t)) t

/-- The cost of a control/state trajectory pair on `[t₀, T]`:
`h(x(T)) + ∫_{t₀}^{T} g(x(t), u(t)) dt`. -/
noncomputable def BertsekasCTCostFrom {n m : ℕ} (M : BertsekasCTModel n m)
    (t₀ : ℝ) (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x : ℝ → EuclideanSpace ℝ (Fin n)) : ℝ :=
  M.h (x M.T) + ∫ t in t₀..M.T, M.g (x t) (u t)

open scoped RealInnerProductSpace in
/-- The Hamiltonian function of Section 3.3.1 of Bertsekas, Vol. I, 3rd ed.:
`H(x, u, p) = g(x, u) + ⟪p, f(x, u)⟫`. -/
noncomputable def BertsekasHamiltonian {n m : ℕ} (M : BertsekasCTModel n m)
    (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) : ℝ :=
  M.g x u + ⟪p, M.f x u⟫


