-- Prove2me | Definitions.Def_DRJointCC_Individual_Supplement_Algorithm
-- name    : DRJointCC_Individual_Supplement_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:28:18.836899+00:00
-- url     : https://prove2.me/theorems/a96660e2-52d3-42ea-892f-e51ef5463437
-- title:
--   p. 23–24 — the set $\bar{\mathcal A}$ and runs of Algorithm 3.1 (Sequential Convex Optimization Procedure)
-- statement:
--   Throughout, $\mathcal P$ is the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, $\Omega=\begin{bmatrix}\Sigma+\mu\mu^\top&\mu\\\mu^\top&1\end{bmatrix}$ is the second-order moment matrix, $\langle X,Y\rangle=\mathrm{Tr}(XY)$, and $\epsilon\in(0,1)$.
--
--   Let $\mathcal J(x,\alpha)=\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon\big(\max_{i}\alpha_i(y_i^0(x)+y_i(x)^\top\tilde\xi)\big)$ be the worst-case CVaR functional (31), $\mathcal X\subseteq\mathbb R^n$ a set, $c\in\mathbb R^n$ a cost vector and $\delta>0$ a tolerance. Put $\bar{\mathcal A}=\{\alpha\in\mathbb R^m:\ \alpha\ge\delta e\}$. Problem (45) for fixed $\alpha$ is $\min\{c^\top x:\ \mathcal J(x,\alpha)\le0,\ x\in\mathcal X\}$, and problem (46) for fixed $x$ is $\min\{\mathcal J(x,\alpha):\ \alpha\in\bar{\mathcal A}\}$.
--
--   A **run of Algorithm 3.1** from $x_{\mathrm{init}}$ is a pair of sequences $(x^t)_{t\ge0}$, $(\alpha^t)_{t\ge1}$ with
--
--   1. $x^0=x_{\mathrm{init}}$;
--   2. for every $t\ge1$, $\alpha^t$ is an optimal solution of (46) with input $x^{t-1}$;
--   3. for every $t\ge1$, $x^t$ is an optimal solution of (45) with input $\alpha^t$.
--
--   The objective values are $f^t=c^\top x^t$. The termination test of Step 4 is not part of the definition: it only stops the run at some $t$.
--
--   This alternating scheme is the paper's heuristic for the biconvex problem (44) over $x$ and $\alpha$; Theorem 3.8 describes its objective values.
--
--   **Formalization Note** The worst-case CVaR functional is the published extended-real `DRJointCC.Joint.Jfun`. Optimality is stated through inequalities against every competitor; the run is any pair of sequences satisfying them, so the definition does not choose among multiple optimal solutions. The entry `α 0` plays no role.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 23 (Ā), p. 24, (45), (46), Algorithm 3.1

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual.Supplement

/-- `Ā = { α : α ≥ δe }`, p. 23, for a tolerance `δ > 0` (the paper sets `δ = 10⁻⁷`). -/
def Abar (m : ℕ) (δ : ℝ) : Set (Fin m → ℝ) := {α | ∀ i, δ ≤ α i}

/-- A run of Algorithm 3.1 (Sequential Convex Optimization Procedure), p. 24, without the
termination test of Step 4, which only truncates the run:
1. `x⁰ = x_init`;
2. for `t ≥ 1`, `α^t` is an optimal solution of (46) with input `x^{t−1}`:
   `α^t ∈ Ā` and `𝒥(x^{t−1}, α^t) ≤ 𝒥(x^{t−1}, α)` for every `α ∈ Ā`;
3. for `t ≥ 1`, `x^t` is an optimal solution of (45) with input `α^t`:
   `x^t ∈ 𝒳`, `𝒥(x^t, α^t) ≤ 0`, and `cᵀx^t ≤ cᵀx` for every `x ∈ 𝒳` with `𝒥(x, α^t) ≤ 0`.
Here `𝒥` is the worst-case CVaR functional (31), `DRJointCC.Joint.Jfun`. The objective value
is `f^t = cᵀx^t`; `α 0` plays no role. -/
def IsAlg31Run {m n k : ℕ} (D : DRJointCC.Joint.JCCData m n k) (μ : Fin k → ℝ)
    (Sig : Matrix (Fin k) (Fin k) ℝ) (ε δ : ℝ) (X : Set (Fin n → ℝ)) (c : Fin n → ℝ)
    (xinit : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (α : ℕ → Fin m → ℝ) : Prop :=
  x 0 = xinit ∧
    (∀ t : ℕ, α (t + 1) ∈ Abar m δ ∧
      ∀ α' ∈ Abar m δ,
        DRJointCC.Joint.Jfun D μ Sig ε (x t) (α (t + 1)) ≤ DRJointCC.Joint.Jfun D μ Sig ε (x t) α') ∧
    (∀ t : ℕ, x (t + 1) ∈ X ∧ DRJointCC.Joint.Jfun D μ Sig ε (x (t + 1)) (α (t + 1)) ≤ 0 ∧
      ∀ x' ∈ X, DRJointCC.Joint.Jfun D μ Sig ε x' (α (t + 1)) ≤ 0 → c ⬝ᵥ x (t + 1) ≤ c ⬝ᵥ x')

end DRJointCC.Individual.Supplement


