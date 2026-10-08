-- Prove2me | Definitions.Def_RegMCBSDE_Simulation_Setting
-- name    : RegMCBSDE_Simulation_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:16.231986+00:00
-- url     : https://prove2.me/theorems/ebea0ac5-b6b4-4f43-8457-596896c3b8a9
-- title:
--   §2.1, (3), pp. 4–7 — model data, (H1)–(H2), the time grid, the Euler scheme and the truncation profile ξ
-- statement:
--   This file fixes the deterministic data of the forward–backward model of Gobet, Lemor and Warin (§2.1) and the objects every later statement shares.
--
--   A **model** consists of a horizon $T$, a drift $b:[0,T]\times\mathbb R^d\to\mathbb R^d$, a diffusion coefficient $\sigma:[0,T]\times\mathbb R^d\to\mathbb R^{d\times q}$, a driver $f:[0,T]\times\mathbb R^d\times\mathbb R\times\mathbb R^q\to\mathbb R$, and two constants $C_f$ and $L$. The standing assumptions are $T>0$ and
--
--   1. **(H1)** $b$ and $\sigma$ are uniformly Lipschitz in $(t,x)$: for $t,t'\in[0,T]$ and $x,x'\in\mathbb R^d$,
--   $$|b(t,x)-b(t',x')|+\|\sigma(t,x)-\sigma(t',x')\|_F\le L\,(|t-t'|+|x-x'|);$$
--   2. **(H2)** for $t_1,t_2\in[0,T]$,
--   $$|f(t_2,x_2,y_2,z_2)-f(t_1,x_1,y_1,z_1)|\le C_f\big(|t_2-t_1|^{1/2}+|x_2-x_1|+|y_2-y_1|+|z_2-z_1|\big).$$
--
--   For $N\ge1$ the time step is $h=T/N$ and the grid is $t_k=kh$. Given $S_0\in\mathbb R^d$ and increments $\Delta W_k\in\mathbb R^q$, the **Euler scheme** (3) is
--   $$S^N_{t_0}=S_0,\qquad S^N_{t_{k+1}}=S^N_{t_k}+b(t_k,S^N_{t_k})\,h+\sigma(t_k,S^N_{t_k})\,\Delta W_k .$$
--
--   A **truncation profile** (p. 7) is a $C^2_b$ function $\xi:\mathbb R\to\mathbb R$ with $\xi(x)=x$ for $|x|\le 3/2$, $|\xi|_\infty\le2$ and $|\xi'|_\infty\le1$. The file also introduces $|x|^2=\sum_i x_i^2$ and $\|A\|_F^2=\sum_{i,j}a_{ij}^2$.
--
--   **Formalization Note** The paper assumes (H1)–(H3); (H3) concerns the terminal functional $\Phi$ of the continuous path, which no statement of this mission involves, so it is dropped. The Lipschitz condition (H1) is written with the Frobenius norm on matrices (all matrix norms are equivalent). Vectors of coefficients are typed as functions, so their Euclidean norm is written out as a sum of squares.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, pp. 4–5, §2.1 (H1)–(H2), Eq. (3); p. 7, truncation profile ξ

import Mathlib

namespace RegMCBSDE.Simulation

open MeasureTheory ProbabilityTheory

/-- `E d` is the Euclidean space `ℝ^d` (Euclidean norm). -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Squared Euclidean norm `|x|² = ∑ᵢ xᵢ²` of a vector `x : ι → ℝ` (written out, because the
default norm on a function type is the sup norm). -/
def sqn {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

/-- Squared Frobenius norm `‖A‖_F² = ∑_{i,j} a_{ij}²` of a real matrix. -/
def frobSq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- The deterministic data of the forward–backward model (§2.1, p. 4): the horizon `T`, the drift
`b : [0,T] × ℝ^d → ℝ^d`, the diffusion `σ : [0,T] × ℝ^d → ℝ^{d×q}`, the driver
`f : [0,T] × ℝ^d × ℝ × ℝ^q → ℝ`, its Lipschitz constant `Cf` of (H2), and a Lipschitz constant
`L` for (H1). -/
structure Model (d q : ℕ) where
  T : ℝ
  b : ℝ → E d → E d
  σ : ℝ → E d → Matrix (Fin d) (Fin q) ℝ
  f : ℝ → E d → ℝ → E q → ℝ
  Cf : ℝ
  L : ℝ

namespace Model

variable {d q : ℕ} (m : Model d q)

/-- (H1): `b` and `σ` are uniformly Lipschitz in `(t, x) ∈ [0,T] × ℝ^d`, with constant `L`
(Frobenius norm on matrices). -/
def H1 : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) m.T, ∀ t' ∈ Set.Icc (0 : ℝ) m.T, ∀ x x' : E d,
    ‖m.b t x - m.b t' x'‖ + Real.sqrt (frobSq (m.σ t x - m.σ t' x')) ≤ m.L * (|t - t'| + ‖x - x'‖)

/-- (H2): `|f(t₂,x₂,y₂,z₂) - f(t₁,x₁,y₁,z₁)| ≤ C_f (|t₂-t₁|^{1/2} + |x₂-x₁| + |y₂-y₁| + |z₂-z₁|)`
for `t₁, t₂ ∈ [0,T]`. -/
def H2 : Prop :=
  ∀ t₁ ∈ Set.Icc (0 : ℝ) m.T, ∀ t₂ ∈ Set.Icc (0 : ℝ) m.T, ∀ (x₁ x₂ : E d) (y₁ y₂ : ℝ) (z₁ z₂ : E q),
    |m.f t₂ x₂ y₂ z₂ - m.f t₁ x₁ y₁ z₁| ≤
      m.Cf * (Real.sqrt |t₂ - t₁| + ‖x₂ - x₁‖ + |y₂ - y₁| + ‖z₂ - z₁‖)

/-- The standing assumptions used in this mission: `T > 0`, (H1) and (H2). -/
def Standing : Prop := 0 < m.T ∧ m.H1 ∧ m.H2

/-- The time step `h = T / N`. -/
noncomputable def h (N : ℕ) : ℝ := m.T / N

/-- The grid time `t_k = k h`. -/
noncomputable def t (N k : ℕ) : ℝ := k * m.h N

/-- The Euler scheme (3), driven pathwise by increments `ΔW`:
`S_{t_0} = S₀`, `S_{t_{k+1}} = S_{t_k} + b(t_k, S_{t_k}) h + σ(t_k, S_{t_k}) ΔW_k`. -/
noncomputable def euler {Ω : Type*} (N : ℕ) (S0 : E d) (ΔW : ℕ → Ω → E q) : ℕ → Ω → E d
  | 0 => fun _ => S0
  | k + 1 => fun ω =>
      euler N S0 ΔW k ω + m.h N • m.b (m.t N k) (euler N S0 ΔW k ω) +
        WithLp.toLp 2 (Matrix.mulVec (m.σ (m.t N k) (euler N S0 ΔW k ω)) (WithLp.ofLp (ΔW k ω)))

end Model

/-- The truncation profile `ξ` of p. 7: a `C²_b` function `ℝ → ℝ` with `ξ(x) = x` for
`|x| ≤ 3/2`, `|ξ|_∞ ≤ 2` and `|ξ'|_∞ ≤ 1`. -/
def IsTruncationFn (ξ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 ξ ∧ (∀ x, |x| ≤ 3 / 2 → ξ x = x) ∧ (∀ x, |ξ x| ≤ 2) ∧ (∀ x, |deriv ξ x| ≤ 1) ∧
    ∃ B : ℝ, ∀ x, |iteratedDeriv 2 ξ x| ≤ B

end RegMCBSDE.Simulation


