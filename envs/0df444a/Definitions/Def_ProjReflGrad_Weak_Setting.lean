-- Prove2me | Definitions.Def_ProjReflGrad_Weak_Setting
-- name    : ProjReflGrad_Weak_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:15:29.222973+00:00
-- url     : https://prove2.me/theorems/45b4eb84-e715-4452-b71b-6086db6d312e
-- title:
--   (1.1), (C1)–(C3), Algorithm 3.1, pp. 1–4 — nearest point and P_C, solution set S, monotone and Lipschitz maps, weak convergence, runs of Algorithm 3.1, residual r
-- statement:
--   Throughout, $H$ is a real inner product space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$ (the theorems add completeness, so that $H$ is a Hilbert space), $C\subseteq H$ is a set and $F:H\to H$ is a mapping. This file fixes the objects of the variational inequality problem and of the projected reflected gradient method.
--
--   1. **Nearest point.** A point $p$ is a nearest point of $C$ to $z$ if $p\in C$ and $\|z-p\|\le\|z-q\|$ for every $q\in C$.
--   2. **Metric projection.** $P_C(z)$ is a nearest point of $C$ to $z$ whenever one exists (chosen arbitrarily if there are several), and $z$ itself otherwise. For $C$ nonempty, closed and convex in a Hilbert space the nearest point exists and is unique, so $P_C$ is the usual metric projection.
--   3. **Solution set.** The variational inequality (1.1) asks for $x^*\in C$ with
--   $$\langle F(x^*),\,x-x^*\rangle\ge 0\qquad\forall x\in C;$$
--   its solution set is denoted $S$.
--   4. **Monotone map (C2).** $F$ is monotone if $\langle F(x)-F(y),x-y\rangle\ge0$ for all $x,y\in H$.
--   5. **Lipschitz map (C3).** $F$ is Lipschitz with constant $L$ if $\|F(x)-F(y)\|\le L\|x-y\|$ for all $x,y\in H$; the theorems require $L>0$.
--   6. **Weak convergence.** $x_n\rightharpoonup x^*$ if $\langle x_n,v\rangle\to\langle x^*,v\rangle$ for every $v\in H$.
--   7. **Runs of Algorithm 3.1.** Sequences $(x_n),(y_n)$ form a run with step $\lambda$ if $y_0=x_0\in H$ and, for every $n$,
--   $$x_{n+1}=P_C\big(x_n-\lambda F(y_n)\big),\qquad y_{n+1}=2x_{n+1}-x_n .$$
--   8. **Projected residual.** $r(x,y)=\|y-P_C(x-\lambda F(y))\|+\|x-y\|$.
--
--   These are the objects of §§1–3 of the paper; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note.** The projection is defined by choice with the junk value $z$ when no nearest point exists; every theorem that uses it assumes $C$ closed, convex and nonempty, so the junk branch is never reached. The run predicate has no stopping rule: a run that would stop at a solution $x_n=y_n\in S$ continues as a constant sequence, so infinite runs subsume stopped ones. The starting point $x_0$ need not lie in $C$, as in Algorithm 3.1.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, pp. 1–4, (1.1), (C1)–(C3), §3 residual r(x, y), Algorithm 3.1; p. 3 weak convergence

import Mathlib

namespace ProjReflGrad.Weak

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `p` is a nearest point of `C` to `z`: `p ∈ C` and `‖z - p‖ ≤ ‖z - q‖` for all `q ∈ C`. -/
def IsProj (C : Set H) (z p : H) : Prop := p ∈ C ∧ ∀ q ∈ C, ‖z - p‖ ≤ ‖z - q‖

/-- The metric projection `P_C z`: a nearest point when one exists, the junk value `z` otherwise.
For `C` nonempty, closed and convex in a Hilbert space the nearest point exists and is unique. -/
noncomputable def proj (C : Set H) (z : H) : H := by
  classical exact if h : ∃ p, IsProj C z p then h.choose else z

/-- The solution set `S` of the variational inequality (1.1):
`x* ∈ C` with `⟨F(x*), x - x*⟩ ≥ 0` for all `x ∈ C`. -/
def solSet (C : Set H) (F : H → H) : Set H :=
  {xs | xs ∈ C ∧ ∀ x ∈ C, 0 ≤ inner ℝ (F xs) (x - xs)}

/-- (C2): `F` is monotone on all of `H`. -/
def IsMonotoneMap (F : H → H) : Prop := ∀ x y : H, 0 ≤ inner ℝ (F x - F y) (x - y)

/-- (C3): `F` is Lipschitz on all of `H` with the real constant `L`. -/
def IsLipschitzMap (F : H → H) (L : ℝ) : Prop := ∀ x y : H, ‖F x - F y‖ ≤ L * ‖x - y‖

/-- Weak convergence `x_n ⇀ xs`: `⟨x_n, v⟩ → ⟨xs, v⟩` for every `v ∈ H`. -/
def IsWeakLimit (x : ℕ → H) (xs : H) : Prop :=
  ∀ v : H, Filter.Tendsto (fun n => inner ℝ (x n) v) Filter.atTop (nhds (inner ℝ xs v))

/-- `(x, y)` is a run of Algorithm 3.1 with step `lam`: `x₀ = y₀ ∈ H` arbitrary,
`x_{n+1} = P_C(x_n - λ F(y_n))` and `y_{n+1} = 2x_{n+1} - x_n` for every `n`. -/
def IsPRGRun (C : Set H) (F : H → H) (lam : ℝ) (x y : ℕ → H) : Prop :=
  y 0 = x 0 ∧ ∀ n : ℕ, x (n + 1) = proj C (x n - lam • F (y n)) ∧ y (n + 1) = (2 : ℝ) • x (n + 1) - x n

/-- The projected residual `r(x, y) = ‖y - P_C(x - λF(y))‖ + ‖x - y‖` of §3. -/
noncomputable def residual (C : Set H) (F : H → H) (lam : ℝ) (x y : H) : ℝ :=
  ‖y - proj C (x - lam • F y)‖ + ‖x - y‖

end ProjReflGrad.Weak


