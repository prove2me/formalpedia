-- Prove2me | Definitions.Def_DRJointCC_Joint_Joint
-- name    : DRJointCC_Joint_Joint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:29.462851+00:00
-- url     : https://prove2.me/theorems/290f16c8-a190-4ab6-a72e-7d2a230835af
-- title:
--   (2), p. 2; p. 13; (28)–(31), pp. 15–16; p. 20 — joint chance constraint data, X^JCC, X°^JCC, Z^JCC(α), Z^JCC and the LMI block of (30)
-- statement:
--   This module defines the distributionally robust joint chance constraint of §3 and its worst-case CVaR approximations. Let $\mathcal P$ be the moment set with mean $\mu$ and covariance $\Sigma$, $\Omega$ the second-order moment matrix and $\epsilon$ a tolerance.
--
--   1. **Data** (p. 2): for $i=1,\dots,m$ and $j=1,\dots,k$, vectors $a_i^0,a_i^j\in\mathbb R^n$ and scalars $b_i^0,b_i^j\in\mathbb R$; the uncertain constraint coefficients are $a_i(\tilde\xi)=a_i^0+\sum_j a_i^j\tilde\xi_j$ and $b_i(\tilde\xi)=b_i^0+\sum_j b_i^j\tilde\xi_j$.
--   2. **Auxiliary affine functions** of the decision $x\in\mathbb R^n$: $y_i^j(x)=(a_i^j)^\top x-b_i^j$ for $j=0,\dots,k$, and $y_i(x)=[y_i^1(x),\dots,y_i^k(x)]^\top$, so that the $i$-th constraint reads $y_i^0(x)+y_i(x)^\top\tilde\xi\le0$.
--   3. **The robust joint chance constraint set** (p. 13)
--   $$
--   \mathcal X^{\mathrm{JCC}}=\Big\{x\in\mathbb R^n:\ \inf_{\mathbb P\in\mathcal P}\mathbb P\big(y_i^0(x)+y_i(x)^\top\tilde\xi\le0\ \ \forall i=1,\dots,m\big)\ge1-\epsilon\Big\},
--   $$
--   and its **strict version** (p. 20)
--   $$
--   \mathcal X^{\mathrm{JCC}}_\circ=\Big\{x\in\mathbb R^n:\ \inf_{\mathbb P\in\mathcal P}\mathbb P\Big(\bigcap_{i=1}^m\{y_i^0(x)+y_i(x)^\top\tilde\xi<0\}\Big)\ge1-\epsilon\Big\}.
--   $$
--   4. **The scaled max-loss** for scaling parameters $\alpha\in\mathbb R^m$: $\xi\mapsto\max_{i=1,\dots,m}\alpha_i\big(y_i^0(x)+y_i(x)^\top\xi\big)$, its worst-case CVaR
--   $$
--   \mathcal J(x,\alpha)=\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon\Big(\max_{i=1,\dots,m}\alpha_i\big(y_i^0(x)+y_i(x)^\top\tilde\xi\big)\Big)
--   $$
--   of (31), and the **worst-case CVaR approximation** $\mathcal Z^{\mathrm{JCC}}(\alpha)=\{x:\mathcal J(x,\alpha)\le0\}$ of (29).
--   5. **The union over scaling parameters** (p. 20): $\mathcal Z^{\mathrm{JCC}}=\bigcup_{\alpha\in\mathcal A}\mathcal Z^{\mathrm{JCC}}(\alpha)$, where $\mathcal A=\{\alpha\in\mathbb R^m:\alpha_i>0\ \forall i\}$ (p. 15).
--   6. **The LMI block of (30)**: for $\beta\in\mathbb R$,
--   $$
--   \begin{bmatrix}0 & \tfrac12\alpha_i y_i(x)\\ \tfrac12\alpha_i y_i(x)^\top & \alpha_i y_i^0(x)-\beta\end{bmatrix}\in\mathbb S^{k+1}.
--   $$
--
--   These are the sets compared in the paper's main result on joint chance constraints and in its semidefinite reformulations.
--
--   **Formalization Note** The index $i$ runs over `Fin m` and $j=1,\dots,k$ over `Fin k`; the printed "$i=1,\dots,n$" in the definition of $y_i^j$ on p. 2 is read as $i=1,\dots,m$, as in (2) on the same page. The printed union "$\bigcup_{\alpha\in\mathcal S}$" on p. 20 is read as the union over $\mathcal A$ of p. 15. $\alpha\in\mathcal A$ is written componentwise, $\alpha_i>0$ for every $i$. The maximum over $i$ is a supremum over `Fin m`; it is the finite maximum when $m\ge1$, and every theorem that uses it assumes $m\ge1$. The LMI block is built with the published `ConvexOptimization.symQuadBlock`, so its lower-left block is the transpose of the upper-right one, $\tfrac12\alpha_i y_i(x)^\top$. The probability of a joint event is the measure of the set of $\xi$ satisfying all $m$ inequalities, under one $\mathbb P$.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 2, (2); p. 13, X^JCC; p. 15, (28)–(29); p. 16, Theorem 3.3 (30) and (31); p. 20, Z^JCC and X°^JCC

import Mathlib
import Definitions.Def_DRJointCC_Individual_Moments

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Joint

/-- The data of the joint chance constraint (2), p. 2: for `i = 1, …, m` and `j = 1, …, k`,
the coefficients `a_i^0 ∈ ℝ^n`, `a_i^j ∈ ℝ^n`, `b_i^0 ∈ ℝ`, `b_i^j ∈ ℝ` of
`a_i(ξ) = a_i^0 + Σ_j a_i^j ξ_j` and `b_i(ξ) = b_i^0 + Σ_j b_i^j ξ_j`. -/
structure JCCData (m n k : ℕ) where
  a0 : Fin m → Fin n → ℝ
  a : Fin m → Fin k → Fin n → ℝ
  b0 : Fin m → ℝ
  b : Fin m → Fin k → ℝ

/-- `y_i^0(x) = (a_i^0)ᵀx − b_i^0` (p. 2). -/
def y0 {m n k : ℕ} (D : JCCData m n k) (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  D.a0 i ⬝ᵥ x - D.b0 i

/-- `y_i(x) = [y_i^1(x), …, y_i^k(x)]ᵀ` with `y_i^j(x) = (a_i^j)ᵀx − b_i^j` (p. 2). -/
def y {m n k : ℕ} (D : JCCData m n k) (i : Fin m) (x : Fin n → ℝ) : Fin k → ℝ :=
  fun j => D.a i j ⬝ᵥ x - D.b i j

/-- The feasible set of the distributionally robust joint chance constraint (p. 13):
`X^JCC = { x : inf_{ℙ ∈ 𝒫} ℙ(y_i^0(x) + y_i(x)ᵀξ̃ ≤ 0 ∀ i = 1, …, m) ≥ 1 − ε }`. -/
def XJCC {m n k : ℕ} (D : JCCData m n k) (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (ε : ℝ) : Set (Fin n → ℝ) :=
  {x | ENNReal.ofReal (1 - ε) ≤
    ⨅ P ∈ DRJointCC.Individual.ambiguitySet μ Sig, P {ξ | ∀ i, y0 D i x + y D i x ⬝ᵥ ξ ≤ 0}}

/-- The strict version (p. 20):
`X°^JCC = { x : inf_{ℙ ∈ 𝒫} ℙ(⋂_i {y_i^0(x) + y_i(x)ᵀξ̃ < 0}) ≥ 1 − ε }`. -/
def XJCCStrict {m n k : ℕ} (D : JCCData m n k) (μ : Fin k → ℝ)
    (Sig : Matrix (Fin k) (Fin k) ℝ) (ε : ℝ) : Set (Fin n → ℝ) :=
  {x | ENNReal.ofReal (1 - ε) ≤
    ⨅ P ∈ DRJointCC.Individual.ambiguitySet μ Sig, P {ξ | ∀ i, y0 D i x + y D i x ⬝ᵥ ξ < 0}}

/-- The scaled max-loss `ξ ↦ max_{i=1,…,m} α_i (y_i^0(x) + y_i(x)ᵀξ)` of (28)–(29), p. 15.
For `m ≥ 1` the supremum over `Fin m` is the finite maximum. -/
noncomputable def maxLoss {m n k : ℕ} (D : JCCData m n k) (α : Fin m → ℝ) (x : Fin n → ℝ) :
    (Fin k → ℝ) → ℝ :=
  fun ξ => ⨆ i : Fin m, α i * (y0 D i x + y D i x ⬝ᵥ ξ)

/-- The worst-case CVaR `𝒥(x, α) = sup_{ℙ ∈ 𝒫} ℙ-CVaR_ε(max_i α_i (y_i^0(x) + y_i(x)ᵀξ̃))`
of (31), p. 16. -/
noncomputable def Jfun {m n k : ℕ} (D : JCCData m n k) (μ : Fin k → ℝ)
    (Sig : Matrix (Fin k) (Fin k) ℝ) (ε : ℝ) (x : Fin n → ℝ) (α : Fin m → ℝ) : EReal :=
  DRJointCC.Individual.wcCVaR ε μ Sig (maxLoss D α x)

/-- The worst-case CVaR approximation for fixed scaling parameters `α`, (29), p. 15:
`Z^JCC(α) = { x : 𝒥(x, α) ≤ 0 }`. -/
def ZJCCα {m n k : ℕ} (D : JCCData m n k) (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (ε : ℝ) (α : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | Jfun D μ Sig ε x α ≤ 0}

/-- The union over all componentwise strictly positive scaling parameters (p. 20):
`Z^JCC = ⋃_{α ∈ 𝒜} Z^JCC(α)`, `𝒜 = {α ∈ ℝ^m : α > 0}` (p. 15). -/
def ZJCC {m n k : ℕ} (D : JCCData m n k) (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (ε : ℝ) : Set (Fin n → ℝ) :=
  ⋃ (α : Fin m → ℝ) (_ : ∀ i, 0 < α i), ZJCCα D μ Sig ε α

/-- The block `[[0, ½α_i y_i(x)], [½α_i y_i(x)ᵀ, α_i y_i^0(x) − β]]` of (30), p. 16, indexed by
`Fin k ⊕ Unit` with the extra coordinate last. -/
noncomputable def lmiBlock {m n k : ℕ} (D : JCCData m n k) (x : Fin n → ℝ) (α : Fin m → ℝ) (β : ℝ)
    (i : Fin m) : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ :=
  ConvexOptimization.symQuadBlock 0 ((α i / 2) • y D i x) (α i * y0 D i x - β)

end DRJointCC.Joint


