-- Prove2me | Definitions.Def_AdaptiveStepIPM_PredCorr_Neighborhoods
-- name    : AdaptiveStepIPM_PredCorr_Neighborhoods
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:14:54.144383+00:00
-- url     : https://prove2.me/theorems/428163a0-ab29-4a33-8510-f21006173a7d
-- title:
--   Strictly feasible LP pairs, duality measure, and Euclidean neighborhood
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $c\in\mathbb R^n$ be given data. The report considers the standard-form linear program and its dual,
--
--   $$\text{(P)}\quad \min\ c^Tx\ \ \text{s.t. } Ax=b,\ x\ge0, \qquad\qquad \text{(D)}\quad \max\ b^Ty\ \ \text{s.t. } A^Ty+s=c,\ s\ge0.$$
--
--   The set $\mathcal F^0$ consists of the pairs $(x,s)\in\mathbb R^n\times\mathbb R^n$ such that $x$ is feasible in (P), $s$ (together with some $y\in\mathbb R^m$) is feasible in (D), and every coordinate of $x$ and of $s$ is strictly positive. For such a pair the **duality measure** and the **Euclidean neighbourhood of the central path** with parameter $\beta$ are
--
--   $$\mu(x,s)=\frac{x^Ts}{n},\qquad \mathcal N_2(\beta)=\bigl\{(x,s)\in\mathcal F^0:\ \|Xs-\mu e\|\le\beta\mu\bigr\},$$
--
--   where $X=\operatorname{diag}(x)$, $e$ is the all-ones vector, $Xs$ is the componentwise product $(x_js_j)_j$, and $\|\cdot\|$ without subscript is the Euclidean ($\ell_2$) norm.
--
--   These objects are the feasible domain, the centrality measure and the neighbourhood used throughout the report; Algorithm 1 keeps its iterates in $\mathcal N_2(1/4)$ and its intermediate iterates in $\mathcal N_2(1/2)$.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`; the report's index $j=1,\dots,n$ is `j : Fin n` (0-based). Primal feasibility reuses the published standard-form LP `LinearOptimization.stdFormLP` ($Ax=b$, $x\ge0$); the dual multiplier $y$ is existential, and $s\ge0$ is implied by $s>0$. The Euclidean norm is defined explicitly as $\sqrt{\sum_j v_j^2}$, because Mathlib's norm on `Fin n → ℝ` is the sup norm. $\mu$ divides by $n$, so it is $0$ when $n=0$; the report's $n$ is at least $1$, and theorems using $\mu$ assume $1\le n$. The parameter $\beta$ is unconstrained here; the report's $\beta\in(0,1)$ is imposed by the theorems.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), pp. 1–2, (P), (D), F⁰, N₂(β)

import Mathlib
import Definitions.Def_LinearOptimization_DualLP

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- The Euclidean norm used without a subscript in the report, p. 2. -/
noncomputable def l2Norm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ j, (v j) ^ 2)

/-- The duality measure μ = xᵀs/n. -/
noncomputable def mu {n : ℕ} (x s : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ s) / (n : ℝ)

/-- The strictly feasible primal and dual pairs F⁰, with the dual multiplier existential. -/
def F0 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (x s : Fin n → ℝ) : Prop :=
  x ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.stdFormLP A b c) ∧
  (∃ y : Fin m → ℝ, Aᵀ *ᵥ y + s = c) ∧
  (∀ j, 0 < x j) ∧ (∀ j, 0 < s j)

/-- The report's Euclidean central-path neighborhood N₂(β), pp. 1–2. -/
def N2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (β : ℝ)
    (x s : Fin n → ℝ) : Prop :=
  F0 A b c x s ∧
  l2Norm (fun j => x j * s j - mu x s) ≤ β * mu x s

end AdaptiveStepIPM.PredCorr


