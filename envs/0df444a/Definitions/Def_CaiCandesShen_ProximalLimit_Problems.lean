-- Prove2me | Definitions.Def_CaiCandesShen_ProximalLimit_Problems
-- name    : CaiCandesShen_ProximalLimit_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:24:03.674471+00:00
-- url     : https://prove2.me/theorems/77bc3977-f248-4d6f-bc06-5de081a68a18
-- title:
--   The constrained nuclear norm problem (1.6), its minimum Frobenius norm solution (3.14) and the proximal problem (3.4)
-- statement:
--   Fix convex constraint functions $f_1,\dots,f_m:\mathbb R^{n_1\times n_2}\to\mathbb R$ and let
--   $$\mathcal C=\{X : f_i(X)\le 0 \text{ for all } i=1,\dots,m\}$$
--   be the feasible set. This file defines four predicates on a matrix $X$.
--
--   1. **Feasibility.** $X\in\mathcal C$.
--   2. **Solution of (1.6).** $X$ solves
--   $$\text{minimize } \|X\|_* \quad\text{subject to } f_i(X)\le 0,\ i=1,\dots,m,$$
--   that is, $X\in\mathcal C$ and $\|X\|_*\le\|X'\|_*$ for every $X'\in\mathcal C$.
--   3. **Minimum Frobenius norm solution (3.14).** $X$ is a solution of (1.6) and $\|X\|_F^2\le\|X'\|_F^2$ for every solution $X'$ of (1.6); that is,
--   $$X = X_\infty := \arg\min_X\{\|X\|_F^2 : X \text{ is a solution of (1.6)}\}.$$
--   4. **Solution of the proximal problem (3.4).** For a parameter $\tau$, $X$ solves
--   $$\text{minimize } f_\tau(X)=\tau\|X\|_*+\tfrac12\|X\|_F^2 \quad\text{subject to } f_i(X)\le 0,\ i=1,\dots,m,$$
--   that is, $X\in\mathcal C$ and $f_\tau(X)\le f_\tau(X')$ for every $X'\in\mathcal C$.
--
--   Theorem 3.1 of the paper compares the solutions of (3.4) with $X_\infty$ as $\tau\to\infty$.
--
--   **Formalization Note** The constraints are a family `f : Fin m → Mat n₁ n₂ → ℝ` of real-valued functions; $m=0$ (no constraints) is allowed. The predicates say "is a minimizer"; they do not assert that a minimizer exists. Convexity and lower semicontinuity of the $f_i$ are not part of these definitions: they are hypotheses of the theorems, as in the paper.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1959 §1.3 Eq. (1.6); p. 1965 §3.2 Eq. (3.4); p. 1967 Theorem 3.1 Eq. (3.14)

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic

namespace CaiCandesShen.ProximalLimit

/-- `X` satisfies the constraints `f_i(X) ≤ 0`, `i = 1, …, m`, of (1.6) and (3.4)
(§1.3, p. 1959; §3.2, p. 1965): `X ∈ C = {X : f_i(X) ≤ 0 ∀ i = 1, …, m}`. -/
def Feasible {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ) (X : Mat n₁ n₂) : Prop :=
  ∀ i, f i X ≤ 0

/-- `X` is a solution of problem (1.6) (§1.3, p. 1959):
`minimize ‖X‖_*  subject to  f_i(X) ≤ 0, i = 1, …, m`. -/
def IsNuclearNormSolution {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ) (X : Mat n₁ n₂) : Prop :=
  Feasible f X ∧ ∀ X', Feasible f X' → nuclearNorm X ≤ nuclearNorm X'

/-- `X` is the minimum Frobenius norm solution of (1.6), eq. (3.14) (p. 1967):
`X_∞ := arg min_X {‖X‖_F² : X is a solution of (1.6)}`. -/
def IsMinFrobeniusSolution {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ) (X : Mat n₁ n₂) : Prop :=
  IsNuclearNormSolution f X ∧
    ∀ X', IsNuclearNormSolution f X' → frobNorm X ^ 2 ≤ frobNorm X' ^ 2

/-- `X` is a solution of the proximal problem (3.4) (§3.2, p. 1965):
`minimize f_τ(X)  subject to  f_i(X) ≤ 0, i = 1, …, m`. -/
def IsProximalSolution {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ) (τ : ℝ) (X : Mat n₁ n₂) :
    Prop :=
  Feasible f X ∧ ∀ X', Feasible f X' → fτ τ X ≤ fτ τ X'

end CaiCandesShen.ProximalLimit


