-- Prove2me | Definitions.Def_BellmanDP_Variational_Approximation
-- name    : BellmanDP_Variational_Approximation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T19:04:29.427076+00:00
-- url     : https://prove2.me/theorems/13568207-08ae-4db7-9af7-129121afa901
-- title:
--   The control problem $f(c,T)=\sup\int_0^T F(x,\varphi)\,dt$ and its discrete approximations $f(c,T,n)$ with step $1/n$
-- statement:
--   This file sets up the objects of Chapter IX, § 12 of Bellman's *Dynamic Programming*: a continuous-time control problem and the sequence of discrete-time problems that approximate it.
--
--   The original problem has a state $x(t)\ge 0$, a control $0\le y(t)\le x(t)$, a running reward $F(x,y)$ and dynamics $dx/dt=G(x,y)$, $x(0)=c$, on the horizon $[0,T]$. Writing $y=\varphi x$ with a **fractional control** $0\le\varphi\le 1$ turns $F$ and $G$ into the functions $\tilde F(x,\varphi)=F(x,\varphi x)$ and $\tilde G(x,\varphi)=G(x,\varphi x)$ (Bellman's "new $F$ and $G$").
--
--   1. **Trajectory.** For a function $G(x,\varphi)$, a control $\varphi(t)$ and an initial value $c$, a continuous function $x$ on $[0,T]$ is a trajectory if $s\mapsto G(x(s),\varphi(s))$ is integrable on $[0,T]$ and
--   $$x(t)=c+\int_0^t G(x(s),\varphi(s))\,ds,\qquad 0\le t\le T .$$
--   2. **Continuous value.** $f(c,T)$ is the supremum of $\int_0^T F(x(t),\varphi(t))\,dt$ over measurable controls with $0\le\varphi(t)\le 1$ on $[0,T]$ and their trajectories $x$.
--   3. **Discrete problem.** For $n\ge 1$ put $N=\lfloor Tn\rfloor$. A discrete control is a sequence $\varphi_0,\dots,\varphi_N\in[0,1]$; its states are
--   $$x_0=c,\qquad x_{k+1}=x_k+\frac{G(x_k,\varphi_k)}{n},$$
--   its payoff is $J_N(\{\varphi_k\},n)=\sum_{k=0}^{N}F(x_k,\varphi_k)/n$, and $f(c,T,n)$ is the maximum of $J_N$ over discrete controls.
--   4. **Step control.** A discrete control $\{\varphi_k\}$ defines the step function $\varphi(t)=\varphi_k$ for $k/n\le t<(k+1)/n$.
--   5. **Assumptions (11) of Theorem 2**, on the original $F(x,y)$, $G(x,y)$: (a) $F$ and $G$ have continuous second partial derivatives; (b) there are constants $p,q,r$ with $px\le G(x,y)\le qx+r$ for $x>0$, $0\le y\le x$; (c) $G_y>0$ for all $x>0$, $0\le y\le x$, or $G_y<0$ for all of them.
--
--   These objects are shared by the Lemma of § 12, by the estimates (12.13), (12.14), (12.17) and by Theorem 2.
--
--   **Formalization Note** The print sets $N=[T/n]$ in (12.5) while using the step $1/n$; the consistent reading $N=\lfloor Tn\rfloor$ is used (see the mission description). The step control is $\varphi(t)=\varphi_{\lfloor tn\rfloor}$. "Max" in (12.3) is a supremum (`sSup`); Theorem 2 asserts that the set of continuous payoffs is nonempty and bounded above. The discrete maximum is also `sSup`, of the values of a continuous function on the cube $[0,1]^{N+1}$. The trajectory is a solution of the integral equation, which allows measurable controls; integrability of the right-hand side and of the reward is required explicitly so that the Bochner integral's value $0$ on non-integrable functions cannot enter.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IX, § 12, Eqs. (12.1)-(12.8), pp. 260-261; Lemma (10a)-(10d), p. 261; Theorem 2, assumptions (11), p. 262

import Mathlib

namespace BellmanDP.Variational

open MeasureTheory Set

/-- Bellman, *Dynamic Programming*, Ch. IX, § 12, p. 260, footnote 6 and Eq. (12.3): the change of
control `y = φ x` "introducing a new F and G". A function `H (x, y)` of the state `x` and the original
control `y` (with `0 ≤ y ≤ x`) becomes the function `H (x, φ x)` of the state and the fractional
control `φ` (with `0 ≤ φ ≤ 1`). -/
def phiForm (H : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x φ => H x (φ * x)

/-- Ch. IX, § 12, Eq. (12.5) (corrected, see the mission description): the number of steps
`N = ⌊T n⌋` of the approximating problem with step size `1 / n` on the horizon `T`. The print has
`N = [T/n]`. -/
noncomputable def horizonSteps (T : ℝ) (n : ℕ) : ℕ :=
  ⌊T * n⌋₊

/-- Ch. IX, § 12, Lemma, (10a), p. 261: the step function with constant value `φ_k` on
`k/n ≤ t < (k + 1)/n`. For `t ≥ 0` the value at `t` is `φ_{⌊t n⌋}`. -/
noncomputable def stepControl (n : ℕ) (φs : ℕ → ℝ) (t : ℝ) : ℝ :=
  φs ⌊t * n⌋₊

/-- Ch. IX, § 12, Eq. (12.6), p. 261: the discrete states `x_0 = c`,
`x_{k+1} = x_k + G (x_k, φ_k) / n`, for a function `G (x, φ)` of state and control. -/
noncomputable def eulerTraj (G : ℝ → ℝ → ℝ) (c : ℝ) (n : ℕ) (φs : ℕ → ℝ) : ℕ → ℝ
  | 0 => c
  | k + 1 => eulerTraj G c n φs k + G (eulerTraj G c n φs k) (φs k) / n

/-- Ch. IX, § 12, Eq. (12.4a), p. 261: `x` is a solution on `[0, T]` of `dx/dt = G (x, φ(t))`,
`x(0) = c`, in integral form (a continuous `x` with integrable right-hand side and
`x(t) = c + ∫_0^t G (x(s), φ(s)) ds` for `0 ≤ t ≤ T`). This is the solution concept that allows
measurable (discontinuous) controls. -/
def IsTrajectory (G : ℝ → ℝ → ℝ) (c : ℝ) (φ : ℝ → ℝ) (T : ℝ) (x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Icc 0 T) ∧
    IntegrableOn (fun s => G (x s) (φ s)) (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, x t = c + ∫ s in (0 : ℝ)..t, G (x s) (φ s)

/-- Ch. IX, § 12, Eq. (12.5), p. 261: `J_N ({φ_k}, n) = Σ_{k=0}^{N} F (x_k, φ_k) / n`, with the
states `x_k` given by (12.6). -/
noncomputable def discretePayoff (F G : ℝ → ℝ → ℝ) (c : ℝ) (n : ℕ) (φs : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), F (eulerTraj G c n φs k) (φs k) / n

/-- Ch. IX, § 12, Eq. (12.8), p. 261: `f (c, T, n) = Max J_N ({φ_k}, n)`, the maximum over the
controls with `0 ≤ φ_k ≤ 1`, `k = 0, 1, …, N` (Eq. (12.7)), where `N = ⌊T n⌋`. -/
noncomputable def discreteValue (F G : ℝ → ℝ → ℝ) (c T : ℝ) (n : ℕ) : ℝ :=
  sSup {J : ℝ | ∃ φs : ℕ → ℝ, (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0 : ℝ) 1) ∧
    J = discretePayoff F G c n φs (horizonSteps T n)}

/-- Ch. IX, § 12, Eqs. (12.3)–(12.4), pp. 260–261: the set of values `∫_0^T F (x, φ) dt` over
measurable controls with `0 ≤ φ(t) ≤ 1` on `[0, T]` and solutions `x` of `dx/dt = G (x, φ)`,
`x(0) = c`. -/
def contPayoffs (F G : ℝ → ℝ → ℝ) (c T : ℝ) : Set ℝ :=
  {J : ℝ | ∃ φ x : ℝ → ℝ, Measurable φ ∧ (∀ t ∈ Icc 0 T, φ t ∈ Icc (0 : ℝ) 1) ∧
    IsTrajectory G c φ T x ∧ IntegrableOn (fun t => F (x t) (φ t)) (Icc 0 T) ∧
    J = ∫ t in (0 : ℝ)..T, F (x t) (φ t)}

/-- Ch. IX, § 12, Eq. (12.3), p. 260: `f (c, T) = Max ∫_0^T F (x, φ) dt`, taken as the supremum of
`contPayoffs`. -/
noncomputable def contValue (F G : ℝ → ℝ → ℝ) (c T : ℝ) : ℝ :=
  sSup (contPayoffs F G c T)

/-- Ch. IX, § 12, Theorem 2, assumptions (11), p. 262, on the original functions `F (x, y)`,
`G (x, y)` of state `x` and control `0 ≤ y ≤ x`:
(a) `F` and `G` have continuous second partial derivatives;
(b) there are constants `p, q, r` with `p x ≤ G (x, y) ≤ q x + r` for `x > 0`, `0 ≤ y ≤ x`;
(c) `G_y` is of one sign: `G_y > 0` for all `x > 0`, `0 ≤ y ≤ x`, or `G_y < 0` for all of them. -/
def Assumptions11 (F G : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 (fun z : ℝ × ℝ => F z.1 z.2) ∧
    ContDiff ℝ 2 (fun z : ℝ × ℝ => G z.1 z.2) ∧
    (∃ p q r : ℝ, ∀ x y : ℝ, 0 < x → 0 ≤ y → y ≤ x → p * x ≤ G x y ∧ G x y ≤ q * x + r) ∧
    ((∀ x y : ℝ, 0 < x → 0 ≤ y → y ≤ x → 0 < deriv (G x) y) ∨
      (∀ x y : ℝ, 0 < x → 0 ≤ y → y ≤ x → deriv (G x) y < 0))

end BellmanDP.Variational


