-- Prove2me | Definitions.Def_SelfDualLP_Output_HLP
-- name    : SelfDualLP_Output_HLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:21.781388+00:00
-- url     : https://prove2.me/theorems/1eb759c8-3845-4bd2-b380-25d3b9c29210
-- title:
--   The homogeneous self-dual program (HLP), its feasible set F_h, strictly feasible set F_h°, and (strictly) self-complementary solutions
-- statement:
--   Fix real data $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$ and an initial triple $x^0,s^0\in\mathbb R^n$, $y^0\in\mathbb R^m$. Put
--
--   $$
--   \bar b=b-Ax^0,\qquad \bar c=c-A^Ty^0-s^0,\qquad \bar z=c^Tx^0+1-b^Ty^0 .
--   $$
--
--   A point of the homogeneous self-dual program (HLP) is a sextuple $(y,x,\tau,\theta,s,\kappa)$ with $y\in\mathbb R^m$, $x,s\in\mathbb R^n$ and $\tau,\theta,\kappa\in\mathbb R$. (HLP) is
--
--   $$
--   \begin{array}{rrrrrl}
--   \min & & & & ((x^0)^Ts^0+1)\theta & \\
--   \text{s.t.} & & Ax & -b\tau & +\bar b\theta & =0,\\
--   & -A^Ty & & +c\tau & -\bar c\theta & \ge 0,\\
--   & b^Ty & -c^Tx & & +\bar z\theta & \ge 0,\\
--   & -\bar b^Ty & +\bar c^Tx & -\bar z\tau & & =-(x^0)^Ts^0-1,
--   \end{array}
--   $$
--
--   with $y$ free, $x\ge0$, $\tau\ge0$, $\theta$ free. The slack of the second row is $s$ and that of the third row is $\kappa$.
--
--   1. $\mathcal F_h$ is the set of points satisfying these constraints with $s=-A^Ty+c\tau-\bar c\theta\ge0$ and $\kappa=b^Ty-c^Tx+\bar z\theta\ge0$.
--   2. $\mathcal F_h^0$ is the set of points of $\mathcal F_h$ with $x>0$, $\tau>0$, $s>0$, $\kappa>0$.
--   3. An **optimal solution** (also called a **self-complementary solution**) is a point of $\mathcal F_h$ whose objective $((x^0)^Ts^0+1)\theta$ is no larger than at any point of $\mathcal F_h$.
--   4. A **strictly self-complementary solution** is an optimal solution with $\theta=0$ and $(x+s;\tau+\kappa)>0$.
--
--   The file also records the paper's choice (7), $y^0=0$, $x^0=s^0=e$ (the all-ones vector), under which $\bar b=b-Ae$, $\bar c=c-e$, $\bar z=c^Te+1$ and the objective is $(n+1)\theta$.
--
--   **Formalization Note** Optimality is defined as minimizing the objective over $\mathcal F_h$, not as $\theta=0$; that the optimal value is zero is Theorem 2 (iv). The instance under (7) is obtained by substitution, not as a separate program.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 56, (HLP) and (5); p. 57, Theorem 2 (v) and (7); p. 58, (8); DOI 10.1287/moor.19.1.53

import Mathlib

open Matrix

namespace SelfDualLP.Output

/-- A point `(y, x, τ, θ, s, κ)` of the homogeneous self-dual program (HLP), with
`y ∈ ℝ^m`, `x, s ∈ ℝ^n` and `τ, θ, κ ∈ ℝ` (Ye–Todd–Mizuno 1994, p. 56). The same type also
carries search directions `(d_y, d_x, d_τ, d_θ, d_s, d_κ)`. -/
structure HLPPoint (m n : ℕ) where
  y : Fin m → ℝ
  x : Fin n → ℝ
  τ : ℝ
  θ : ℝ
  s : Fin n → ℝ
  κ : ℝ

namespace HLPPoint

/-- `z + α d`, componentwise. -/
def move {m n : ℕ} (z d : HLPPoint m n) (α : ℝ) : HLPPoint m n :=
  ⟨z.y + α • d.y, z.x + α • d.x, z.τ + α * d.τ, z.θ + α * d.θ, z.s + α • d.s, z.κ + α * d.κ⟩

/-- `λ z`, componentwise. -/
def smul {m n : ℕ} (l : ℝ) (z : HLPPoint m n) : HLPPoint m n :=
  ⟨l • z.y, l • z.x, l * z.τ, l * z.θ, l • z.s, l * z.κ⟩

end HLPPoint

/-- `b̄ = b − Ax⁰` (5). -/
def bbar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x0 : Fin n → ℝ) :
    Fin m → ℝ :=
  b - A *ᵥ x0

/-- `c̄ = c − Aᵀy⁰ − s⁰` (5). -/
def cbar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y0 : Fin m → ℝ)
    (s0 : Fin n → ℝ) : Fin n → ℝ :=
  c - Aᵀ *ᵥ y0 - s0

/-- `z̄ = cᵀx⁰ + 1 − bᵀy⁰` (5). -/
def zbar {m n : ℕ} (b : Fin m → ℝ) (c : Fin n → ℝ) (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) : ℝ :=
  c ⬝ᵥ x0 + 1 - b ⬝ᵥ y0

/-- `z ∈ 𝓕_h`: the point is feasible for (HLP) built from `(x⁰, y⁰, s⁰)`, with `s` and `κ`
equal to the slacks of (2) and (3):
(1) `Ax − bτ + b̄θ = 0`; (2) `s = −Aᵀy + cτ − c̄θ`; (3) `κ = bᵀy − cᵀx + z̄θ`;
(4) `−b̄ᵀy + c̄ᵀx − z̄τ = −(x⁰)ᵀs⁰ − 1`; `x ≥ 0`, `τ ≥ 0`, `s ≥ 0`, `κ ≥ 0`; `y`, `θ` free. -/
def HLPFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ) (z : HLPPoint m n) : Prop :=
  A *ᵥ z.x - z.τ • b + z.θ • bbar A b x0 = 0 ∧
  z.s = -(Aᵀ *ᵥ z.y) + z.τ • c - z.θ • cbar A c y0 s0 ∧
  z.κ = b ⬝ᵥ z.y - c ⬝ᵥ z.x + zbar b c x0 y0 * z.θ ∧
  -(bbar A b x0 ⬝ᵥ z.y) + cbar A c y0 s0 ⬝ᵥ z.x - zbar b c x0 y0 * z.τ = -(x0 ⬝ᵥ s0) - 1 ∧
  (∀ j, 0 ≤ z.x j) ∧ 0 ≤ z.τ ∧ (∀ j, 0 ≤ z.s j) ∧ 0 ≤ z.κ

/-- `z ∈ 𝓕_h°`: `z ∈ 𝓕_h` and `(x, τ, s, κ) > 0` componentwise. -/
def HLPStrictlyFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ) (z : HLPPoint m n) :
    Prop :=
  HLPFeasible A b c x0 y0 s0 z ∧ (∀ j, 0 < z.x j) ∧ 0 < z.τ ∧ (∀ j, 0 < z.s j) ∧ 0 < z.κ

/-- The objective `((x⁰)ᵀs⁰ + 1)θ` of (HLP). -/
def hlpObjective {m n : ℕ} (x0 s0 : Fin n → ℝ) (z : HLPPoint m n) : ℝ :=
  (x0 ⬝ᵥ s0 + 1) * z.θ

/-- `z` is an optimal solution of (HLP) (a self-complementary solution): `z ∈ 𝓕_h` and its
objective value is `≤` that of every point of `𝓕_h`. -/
def HLPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ) (z : HLPPoint m n) : Prop :=
  HLPFeasible A b c x0 y0 s0 z ∧
    ∀ z', HLPFeasible A b c x0 y0 s0 z' → hlpObjective x0 s0 z ≤ hlpObjective x0 s0 z'

/-- `z` is a strictly self-complementary solution of (HLP): an optimal solution with `θ = 0`
and `(x + s; τ + κ) > 0` (Theorem 2 (v), p. 57). -/
def StrictlySelfComplementary {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ) (z : HLPPoint m n) :
    Prop :=
  HLPOptimal A b c x0 y0 s0 z ∧ z.θ = 0 ∧ (∀ j, 0 < z.x j + z.s j) ∧ 0 < z.τ + z.κ

/-! The choice (7) `y⁰ = 0, x⁰ = e, s⁰ = e` (p. 57), under which `b̄ = b − Ae`, `c̄ = c − e`,
`z̄ = cᵀe + 1` (8) and the objective is `(n + 1)θ`. -/

/-- The all-ones vector `e`. -/
def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- `𝓕_h` under (7). -/
def HLPFeasible7 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) : Prop :=
  HLPFeasible A b c (ones n) 0 (ones n) z

/-- `𝓕_h°` under (7). -/
def HLPStrictlyFeasible7 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z : HLPPoint m n) : Prop :=
  HLPStrictlyFeasible A b c (ones n) 0 (ones n) z

/-- Optimal solution of (HLP) under (7). -/
def HLPOptimal7 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) : Prop :=
  HLPOptimal A b c (ones n) 0 (ones n) z

/-- Strictly self-complementary solution of (HLP) under (7). -/
def StrictlySelfComplementary7 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z : HLPPoint m n) : Prop :=
  StrictlySelfComplementary A b c (ones n) 0 (ones n) z

end SelfDualLP.Output


