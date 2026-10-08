-- Prove2me | Definitions.Def_BilinearGramian_Kernel_System
-- name    : BilinearGramian_Kernel_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:25.189858+00:00
-- url     : https://prove2.me/theorems/47cc9cae-d6c2-4f60-b56c-34f1d5ad22e3
-- title:
--   The bilinear control system (3.1), the homogeneous system (3.5), admissible inputs and solutions
-- statement:
--   Fix integers $n, m \ge 0$, matrices $A \in \mathbb R^{n\times n}$, $N_1,\dots,N_m \in \mathbb R^{n\times n}$ and $B \in \mathbb R^{n\times m}$. The **bilinear control system** (3.1) is
--   $$\dot x = Ax + \sum_{j=1}^m N_j x\, u_j + Bu, \qquad x(t)\in\mathbb R^n,\quad u(t) = [u_1(t),\dots,u_m(t)]^T \in \mathbb R^m,$$
--   and the **homogeneous bilinear system** (3.5) is the same equation without the term $Bu$:
--   $$\dot x = Ax + \sum_{j=1}^m N_j x\, u_j .$$
--   The same $m$ counts the bilinear terms and the columns of $B$. This file fixes the vector fields
--   $$f(z,w) = Az + \sum_{j=1}^m w_j N_j z + Bw, \qquad f_0(z,w) = Az + \sum_{j=1}^m w_j N_j z$$
--   for a state $z\in\mathbb R^n$ and an input value $w\in\mathbb R^m$, and the notion of solution used throughout the mission:
--
--   1. An **admissible input** is a function $u : [0,\infty) \to \mathbb R^m$ that is integrable on every compact interval $[0,T]$. This class contains $L^2[0,\infty[$, the inputs of the energy functionals of the paper.
--   2. Given an input $u$ and an initial state $x_0$, a **solution** of (3.1) on $[0,\infty)$ is a function $x:[0,\infty)\to\mathbb R^n$, continuous on $[0,\infty)$, such that $s\mapsto f(x(s),u(s))$ is integrable on every $[0,t]$ and
--   $$x(t) = x_0 + \int_0^t \Big(Ax(s) + \sum_{j=1}^m u_j(s) N_j x(s) + Bu(s)\Big)\,ds \qquad\text{for all } t\ge 0 .$$
--   3. A solution of (3.5) is defined in the same way with $f_0$ in place of $f$.
--
--   This is the standard (Carathéodory) meaning of "the solution $x(t,x_0,u)$ of (3.1)" for inputs that are only integrable; for continuous inputs it coincides with the classical $C^1$ solution. The output of the system is $y = Cx$ (3.2), written directly in the theorems.
--
--   **Formalization Note** States are `Fin n → ℝ`, inputs `ℝ → Fin m → ℝ`; the paper's index $j = 1,\dots,m$ is `Fin m`. Values of $u$ and $x$ at negative times play no role. The integrability of the integrand is part of the solution predicate, so the Bochner integral never takes its junk value $0$.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 694, eqs. (3.1)–(3.2); p. 695, eq. (3.5)

import Mathlib

open Matrix

namespace BilinearGramian.Kernel

/-- The right-hand side of the bilinear control system (3.1) of Benner–Damm (SIAM J. Control
Optim. 49(2) (2011), p. 694):
`f(z, w) = A z + ∑_{j=1}^m N_j z w_j + B w` for a state `z ∈ ℝⁿ` and an input value `w ∈ ℝᵐ`.
The paper's indices `j = 1, …, m` are `Fin m`. -/
def field {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (N : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (z : Fin n → ℝ) (w : Fin m → ℝ) : Fin n → ℝ :=
  A *ᵥ z + ∑ j, w j • (N j *ᵥ z) + B *ᵥ w

/-- The right-hand side of the homogeneous bilinear system (3.5) (p. 695):
`f₀(z, w) = A z + ∑_{j=1}^m N_j z w_j`, i.e. (3.1) without the term `B w`. -/
def homField {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (N : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℝ) (w : Fin m → ℝ) : Fin n → ℝ :=
  A *ᵥ z + ∑ j, w j • (N j *ᵥ z)

/-- Admissible input functions `u : [0, ∞) → ℝᵐ`: integrable on every compact interval `[0, T]`.
This class contains `L²[0, ∞[`, the inputs of the paper's energy functionals (3.3)–(3.4).
Values of `u` at negative times are irrelevant. -/
def IsInput {m : ℕ} (u : ℝ → Fin m → ℝ) : Prop :=
  ∀ T : ℝ, MeasureTheory.IntegrableOn u (Set.Icc 0 T)

/-- `x` is a (Carathéodory) solution on `[0, ∞)` of the bilinear system (3.1) with input `u` and
initial state `x(0) = x0`: `x` is continuous on `[0, ∞)`, the integrand `s ↦ f(x(s), u(s))` is
integrable on every `[0, t]`, and
`x(t) = x0 + ∫₀ᵗ (A x(s) + ∑_j N_j x(s) u_j(s) + B u(s)) ds` for all `t ≥ 0`. -/
def IsSolution {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (N : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (u : ℝ → Fin m → ℝ) (x0 : Fin n → ℝ) (x : ℝ → Fin n → ℝ) :
    Prop :=
  ContinuousOn x (Set.Ici 0) ∧
    ∀ t : ℝ, 0 ≤ t →
      IntervalIntegrable (fun s => field A N B (x s) (u s)) MeasureTheory.volume 0 t ∧
        x t = x0 + ∫ s in (0 : ℝ)..t, field A N B (x s) (u s)

/-- `x` is a (Carathéodory) solution on `[0, ∞)` of the homogeneous bilinear system (3.5) with
input `u` and initial state `x(0) = x0`: `x` is continuous on `[0, ∞)`, the integrand is integrable
on every `[0, t]`, and `x(t) = x0 + ∫₀ᵗ (A x(s) + ∑_j N_j x(s) u_j(s)) ds` for all `t ≥ 0`. -/
def IsHomSolution {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (N : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ → Fin m → ℝ) (x0 : Fin n → ℝ) (x : ℝ → Fin n → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧
    ∀ t : ℝ, 0 ≤ t →
      IntervalIntegrable (fun s => homField A N (x s) (u s)) MeasureTheory.volume 0 t ∧
        x t = x0 + ∫ s in (0 : ℝ)..t, homField A N (x s) (u s)

end BilinearGramian.Kernel


