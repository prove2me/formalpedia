-- Prove2me | Definitions.Def_AdaptiveStepIPM_Potential_StandardLP
-- name    : AdaptiveStepIPM_Potential_StandardLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:09.449408+00:00
-- url     : https://prove2.me/theorems/e7fbc382-713a-4674-acab-fa0a3502e8b2
-- title:
--   The standard-form primal–dual linear program and its strictly feasible set $\mathcal F^0$
-- statement:
--   Fix integers $m,n \ge 0$, a matrix $A \in \mathbb R^{m\times n}$, and vectors $b \in \mathbb R^m$ and $c \in \mathbb R^n$. The standard-form **primal linear program** and its **dual** are
--   $$
--   \text{(P)}\quad \min\ c^Tx\quad\text{subject to }Ax=b,\ x\ge0,
--   \qquad
--   \text{(D)}\quad \max\ b^Ty\quad\text{subject to }A^Ty+s=c,\ s\ge0.
--   $$
--   The dual vector $y$ is unrestricted in sign.
--
--   The **strictly feasible set** is
--   $$
--   \mathcal F^0=\{(x,s):x>0,\ s>0,\ Ax=b,\ \exists y\in\mathbb R^m,\ A^Ty+s=c\}.
--   $$
--   The module also records the ordinary nonnegative feasibility relations for (P) and (D).
--
--   This standard-form LP pair is the common feasible model for the report's algorithms; the neighborhood and potential reduction rules are defined on top of it.
--
--   **Formalization Note** Vectors use `Fin n → ℝ` and matrices use `Matrix (Fin m) (Fin n) ℝ`. The pair $(x,s)$ stores no particular dual witness $y$; strict dual feasibility requires one to exist. Theorems involving $\mu=x^Ts/n$ separately assume $n\ge1$.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 1, (P), (D), F⁰

import Mathlib

/-!
Mizuno, Todd, Ye, *On adaptive-step primal-dual interior-point algorithms for linear
programming*, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), §1, p. 1.

The standard-form primal problem (P) minimizes `cᵀx` subject to `Ax = b`, `x ≥ 0`;
its dual (D) maximizes `bᵀy` subject to `Aᵀy + s = c`, `s ≥ 0`. The paper's `F⁰`
consists of pairs `(x, s)` for which `x` and `s` are strictly positive and some `y`
makes the two equalities hold. Dual variables `y` have no sign restriction.
-/

open Matrix

namespace AdaptiveStepIPM.Potential

/-- The data `(A, b, c)` of the standard-form primal–dual LP pair (P), (D), p. 1. -/
structure StandardLP (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ

/-- Feasibility for the standard-form primal problem (P), p. 1. -/
def StandardLP.PrimalFeasible {m n : ℕ} (L : StandardLP m n) (x : Fin n → ℝ) : Prop :=
  L.A *ᵥ x = L.b ∧ ∀ j, 0 ≤ x j

/-- Feasibility for the dual problem (D), p. 1. The multiplier `y` is free. -/
def StandardLP.DualFeasible {m n : ℕ} (L : StandardLP m n)
    (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  L.Aᵀ *ᵥ y + s = L.c ∧ ∀ j, 0 ≤ s j

/-- The strictly feasible set `F⁰` (p. 1): `x > 0`, `s > 0`, `Ax = b`, and `Aᵀy + s = c`
for some `y ∈ ℝᵐ`. -/
def StandardLP.StrictlyFeasible {m n : ℕ} (L : StandardLP m n)
    (x s : Fin n → ℝ) : Prop :=
  (∀ j, 0 < x j) ∧ (∀ j, 0 < s j) ∧ L.A *ᵥ x = L.b ∧
    ∃ y : Fin m → ℝ, L.Aᵀ *ᵥ y + s = L.c

end AdaptiveStepIPM.Potential


