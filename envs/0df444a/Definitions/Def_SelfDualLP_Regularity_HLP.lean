-- Prove2me | Definitions.Def_SelfDualLP_Regularity_HLP
-- name    : SelfDualLP_Regularity_HLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:24.040983+00:00
-- url     : https://prove2.me/theorems/7736ee94-8eb7-4b01-8a54-f0486c5f4daa
-- title:
--   The homogeneous self-dual program (HLP), feasible points, and optimality
-- statement:
--   Fix initial vectors $x^0,s^0\in\mathbb R^n$ with positive coordinates and $y^0\in\mathbb R^m$. Set
--   $$
--   \bar b=b-Ax^0,\qquad \bar c=c-A^Ty^0-s^0,\qquad
--   \bar z=c^Tx^0+1-b^Ty^0.
--   $$
--   A point of (HLP) is $(y,x,\tau,\theta,s,\kappa)$. It is feasible when $x,s,\tau,\kappa\ge0$; $y$ and $\theta$ are free; and
--   $$
--   Ax-b\tau+\bar b\theta=0,\quad
--   s=-A^Ty+c\tau-\bar c\theta,\quad
--   \kappa=b^Ty-c^Tx+\bar z\theta,\quad
--   -\bar b^Ty+\bar c^Tx-\bar z\tau=-(x^0)^Ts^0-1.
--   $$
--   The objective is to minimize $((x^0)^Ts^0+1)\theta$. Strict feasibility makes every coordinate of $x$ and $s$, and both $\tau$ and $\kappa$, positive. An optimal point minimizes the objective over the entire feasible set. Under the paper's later choice $y^0=0$ and $x^0=s^0=e$ (the all-ones vector), the paper calls any optimal point **self-complementary**.
--
--   These definitions are shared by the three formal claims supporting Theorem 9. Optimality is a minimization property; the fact that optimal points have $\theta=0$ belongs to Theorem 2(iv).
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), pp. 56–58, (HLP), (5), (7), (8), F_h and F_h⁰, and p. 57 after Theorem 2(v); DOI 10.1287/moor.19.1.53

import Definitions.Def_SelfDualLP_Regularity_LPData

open Matrix

namespace SelfDualLP.Regularity

/-- A point `(y,x,τ,θ,s,κ)` of the paper's homogeneous program (HLP). -/
structure HLPPoint (m n : ℕ) where
  y : Fin m → ℝ
  x : Fin n → ℝ
  τ : ℝ
  θ : ℝ
  s : Fin n → ℝ
  κ : ℝ

/-- `b̄ = b - Ax⁰` from (5). -/
def bBar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x₀ : Fin n → ℝ) : Fin m → ℝ :=
  b - A *ᵥ x₀

/-- `c̄ = c - Aᵀy⁰ - s⁰` from (5). -/
def cBar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ) : Fin n → ℝ :=
  c - Aᵀ *ᵥ y₀ - s₀

/-- `z̄ = cᵀx⁰ + 1 - bᵀy⁰` from (5). -/
def zBar {m n : ℕ} (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) : ℝ :=
  c ⬝ᵥ x₀ + 1 - b ⬝ᵥ y₀

/-- The objective `((x⁰)ᵀs⁰ + 1)θ` of (HLP). -/
def HLPObjective {m n : ℕ} (x₀ s₀ : Fin n → ℝ) (w : HLPPoint m n) : ℝ :=
  (x₀ ⬝ᵥ s₀ + 1) * w.θ

/-- Feasibility for (HLP), including exact definitions of the slacks `s` and `κ`.
The four equations follow rows (1)--(4) on p. 56 in the order `(y,x,τ,θ)`. -/
def HLPFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (w : HLPPoint m n) : Prop :=
  A *ᵥ w.x - w.τ • b + w.θ • bBar A b x₀ = 0 ∧
  w.s = -(Aᵀ *ᵥ w.y) + w.τ • c - w.θ • cBar A c y₀ s₀ ∧
  w.κ = b ⬝ᵥ w.y - c ⬝ᵥ w.x + zBar b c x₀ y₀ * w.θ ∧
  -(bBar A b x₀ ⬝ᵥ w.y) + cBar A c y₀ s₀ ⬝ᵥ w.x -
      zBar b c x₀ y₀ * w.τ = -(x₀ ⬝ᵥ s₀) - 1 ∧
  (∀ j, 0 ≤ w.x j) ∧ 0 ≤ w.τ ∧ (∀ j, 0 ≤ w.s j) ∧ 0 ≤ w.κ

/-- The strictly feasible set `Fₕ°`: the nonnegative fields are strictly positive. -/
def HLPStrictlyFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (w : HLPPoint m n) : Prop :=
  HLPFeasible A b c x₀ y₀ s₀ w ∧
    (∀ j, 0 < w.x j) ∧ 0 < w.τ ∧ (∀ j, 0 < w.s j) ∧ 0 < w.κ

/-- Optimality means minimizing the HLP objective over all of `Fₕ`. -/
def IsHLPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (w : HLPPoint m n) : Prop :=
  HLPFeasible A b c x₀ y₀ s₀ w ∧
    ∀ v, HLPFeasible A b c x₀ y₀ s₀ v →
      HLPObjective x₀ s₀ w ≤ HLPObjective x₀ s₀ v

/-- The paper's choice (7): `y⁰ = 0`, `x⁰ = s⁰ = e`. -/
def IsSelfComplementary {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (w : HLPPoint m n) : Prop :=
  IsHLPOptimal A b c (fun _ => 1) (fun _ => 0) (fun _ => 1) w

end SelfDualLP.Regularity


