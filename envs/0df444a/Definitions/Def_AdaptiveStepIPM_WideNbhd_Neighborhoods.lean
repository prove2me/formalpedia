-- Prove2me | Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
-- name    : AdaptiveStepIPM_WideNbhd_Neighborhoods
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:25.943069+00:00
-- url     : https://prove2.me/theorems/32e92fd7-d4a8-41e7-8fe6-06e44db575a2
-- title:
--   The feasible interior $\mathcal F^0$, $\mu = x^Ts/n$, the norms $\|\cdot\|_\infty^{\pm}$ and the wide neighbourhoods $\mathcal N_\infty(\beta)$, $\mathcal N_\infty^-(\beta)$
-- statement:
--   Fix integers $n \ge 1$ and $m \ge 0$, a real matrix $A \in \mathbb R^{m\times n}$, and vectors $b \in \mathbb R^m$, $c \in \mathbb R^n$. Mizuno, Todd and Ye consider the standard-form linear program and its dual
--   $$
--   \text{(P)}\quad \min\ c^Tx \ \text{ s.t. } Ax = b,\ x \ge 0, \qquad\qquad \text{(D)}\quad \max\ b^Ty \ \text{ s.t. } A^Ty + s = c,\ s \ge 0 .
--   $$
--   This module defines the objects in which their wide-neighbourhood algorithms live.
--
--   1. The **strictly feasible pairs** $\mathcal F^0$: the pairs $(x,s)\in\mathbb R^n\times\mathbb R^n$ with $x>0$, $s>0$, $Ax=b$, and $A^Ty+s=c$ for some $y\in\mathbb R^m$.
--   2. The **duality measure** $\mu = x^Ts/n$.
--   3. The norms: $\|z\|_\infty = \max_j |z_j|$; $\|z\|^-_\infty := \|z^-\|_\infty$ and $\|z\|^+_\infty := \|z^+\|_\infty$, where $(z^-)_j = \min\{z_j,0\}$ and $(z^+)_j = \max\{z_j,0\}$; and the Euclidean norm $\|z\| = (\sum_j z_j^2)^{1/2}$.
--   4. The **wide neighbourhoods**, for $\beta\in(0,1)$, with $X=\operatorname{diag}(x)$ and $e=(1,\dots,1)^T$:
--   $$
--   \mathcal N_\infty(\beta) = \{(x,s)\in\mathcal F^0 : \|Xs-\mu e\|_\infty \le \beta\mu\},\qquad
--   \mathcal N^-_\infty(\beta) = \{(x,s)\in\mathcal F^0 : \|Xs-\mu e\|^-_\infty \le \beta\mu\},
--   $$
--   where $\mu = x^Ts/n$. Membership in $\mathcal N^-_\infty(\beta)$ says exactly that $x_js_j \ge (1-\beta)\mu$ for every $j$; the products may exceed $\mu$ by any amount.
--
--   These are the neighbourhoods of the central path in which Algorithm 2 keeps its iterates; $\mathcal N^-_\infty(\beta)$ with $\beta$ close to $1$ covers almost all of $\mathcal F^0$.
--
--   **Formalization Note** A pair $(x,s)$ is an element of $(\mathrm{Fin}\,n\to\mathbb R)\times(\mathrm{Fin}\,n\to\mathbb R)$; coordinates are indexed $0,\dots,n-1$ for the paper's $1,\dots,n$. Mathlib's default norm on $\mathrm{Fin}\,n\to\mathbb R$ is the sup norm, so $\|z\|_\infty$ is written as the supremum of $|z_j|$ over the finitely many coordinates and the $\ell_2$ norm is defined explicitly. $\mu$ divides by $n$ as a real number. The data $A,b,c$ are parameters of the neighbourhoods.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), pp. 1–2, (P), (D), F⁰, N∞(β), N∞⁻(β), ‖·‖±∞

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Neighborhoods

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- The strictly feasible primal-dual pairs `F⁰` of Mizuno–Todd–Ye, §1, p. 1: pairs `(x, s)` with
`x > 0`, `s > 0`, `Ax = b`, and `Aᵀy + s = c` for some `y ∈ ℝᵐ`. -/
def strictlyFeasible {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ j, 0 < p.1 j) ∧ (∀ j, 0 < p.2 j) ∧ A *ᵥ p.1 = b ∧ ∃ y : Fin m → ℝ, Aᵀ *ᵥ y + p.2 = c}

/-- The usual `ℓ_∞` norm `‖z‖_∞ = max_j |z_j|` (p. 2), written as a supremum over the finitely
many coordinates (it is `0` when `n = 0`). -/
noncomputable def normInf {n : ℕ} (z : Fin n → ℝ) : ℝ := ⨆ j, |z j|

/-- `‖z‖⁻_∞ := ‖z⁻‖_∞` with `(z⁻)_j := min{z_j, 0}` (p. 2). -/
noncomputable def normInfNeg {n : ℕ} (z : Fin n → ℝ) : ℝ := normInf (fun j => min (z j) 0)

/-- `‖z‖⁺_∞ := ‖z⁺‖_∞` with `(z⁺)_j := max{z_j, 0}` (p. 2). -/
noncomputable def normInfPos {n : ℕ} (z : Fin n → ℝ) : ℝ := normInf (fun j => max (z j) 0)

/-- The Euclidean norm `‖z‖ = (∑_j z_j²)^{1/2}`; on p. 2, `‖·‖` without subscript is the `ℓ₂`
norm. (Mathlib's default norm on `Fin n → ℝ` is the sup norm, hence the explicit definition.) -/
noncomputable def norm2 {n : ℕ} (z : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, z j ^ 2)

/-- The wide neighbourhood `N_∞(β) = {(x, s) ∈ F⁰ : ‖Xs − μe‖_∞ ≤ βμ}`, `μ = xᵀs/n` (p. 2). -/
def Ninf {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (β : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ strictlyFeasible A b c ∧
    normInf (fun j => p.1 j * p.2 j - AdaptiveStepIPM.PredCorr.mu p.1 p.2) ≤ β * AdaptiveStepIPM.PredCorr.mu p.1 p.2}

/-- The wide neighbourhood `N_∞⁻(β) = {(x, s) ∈ F⁰ : ‖Xs − μe‖⁻_∞ ≤ βμ}`, `μ = xᵀs/n` (p. 2). -/
def NinfMinus {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (β : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ strictlyFeasible A b c ∧
    normInfNeg (fun j => p.1 j * p.2 j - AdaptiveStepIPM.PredCorr.mu p.1 p.2) ≤ β * AdaptiveStepIPM.PredCorr.mu p.1 p.2}

end AdaptiveStepIPM.WideNbhd


