-- Prove2me | Definitions.Def_DRJointCC_Individual_Supplement_Bonferroni
-- name    : DRJointCC_Individual_Supplement_Bonferroni
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:26:08.344807+00:00
-- url     : https://prove2.me/theorems/6ed4b256-50b8-4066-b362-c5271b310e39
-- title:
--   p. 14 — safety factors $\mathcal E$ and the Bonferroni approximation $\mathcal Z_B^{\mathrm{JCC}}(\boldsymbol\epsilon)$
-- statement:
--   Throughout, $\mathcal P$ is the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, $\Omega=\begin{bmatrix}\Sigma+\mu\mu^\top&\mu\\\mu^\top&1\end{bmatrix}$ is the second-order moment matrix, $\langle X,Y\rangle=\mathrm{Tr}(XY)$, and $\epsilon\in(0,1)$.
--
--   Consider the joint chance constraint with rows $y_i^0(x)+y_i(x)^\top\tilde\xi\le0$, $i=1,\dots,m$, where $y_i^j(x)=(a_i^j)^\top x-b_i^j$ (p. 2). The set of **safety factors** is
--
--   $$
--   \mathcal E=\Big\{\boldsymbol\epsilon\in\mathbb R^m_+:\ \sum_{i=1}^m\epsilon_i\le\epsilon\Big\}.
--   $$
--
--   For $\boldsymbol\epsilon\in\mathcal E$, the **Bonferroni approximation** $\mathcal Z_B^{\mathrm{JCC}}(\boldsymbol\epsilon)$ is the set of $x\in\mathbb R^n$ such that for every $i=1,\dots,m$ there are $\beta_i\in\mathbb R$ and $M_i\in\mathbb S^{k+1}$ with
--
--   $$
--   M_i\succeq0,\qquad \beta_i+\frac1{\epsilon_i}\langle\Omega,M_i\rangle\le0,\qquad M_i-\begin{bmatrix}0&\frac12y_i(x)\\\frac12y_i(x)^\top&y_i^0(x)-\beta_i\end{bmatrix}\succeq0 .
--   $$
--
--   This is the LMI form of the system of individual chance constraints $\inf_{\mathbb P\in\mathcal P}\mathbb P(y_i^0(x)+y_i(x)^\top\tilde\xi\le0)\ge1-\epsilon_i$, $i=1,\dots,m$, which Bonferroni's inequality turns into a conservative approximation of the joint chance constraint (Theorem 3.1).
--
--   **Formalization Note** $\mathcal E$ allows $\epsilon_i=0$, where $\frac1{\epsilon_i}$ is undefined. The scalar constraint is encoded as $\epsilon_i\beta_i+\langle\Omega,M_i\rangle\le0$ and $\beta_i\le0$. For $\epsilon_i>0$ this is equivalent to the printed constraint, because $\langle\Omega,M_i\rangle\ge0$ when $\Omega\succ0$ and $M_i\succeq0$. At $\epsilon_i=0$ it is the extended-real reading ($\langle\Omega,M_i\rangle=0$, $\beta_i\le0$), and it avoids Lean's convention $1/0=0$, under which row $i$ would become vacuous. The data $a_i^j,b_i^j$ and $y_i^0,y_i$ are the published `DRJointCC.Joint.JCCData`, `y0`, `y`; rows are indexed by `Fin m`.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 14, §3.1 (ℰ, (26), Z_B^JCC(𝛜))

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual.Supplement

/-- The set of safety factors `ℰ = { 𝛜 ∈ ℝ^m_+ : Σ_{i=1}^m ε_i ≤ ε }`, p. 14. -/
def safetyFactors (m : ℕ) (ε : ℝ) : Set (Fin m → ℝ) :=
  {e | (∀ i, 0 ≤ e i) ∧ ∑ i, e i ≤ ε}

/-- The Bonferroni approximation `𝒵_B^JCC(𝛜)`, p. 14: `x` belongs to it iff for every row
`i` there are `β_i ∈ ℝ` and `M_i ∈ 𝕊^{k+1}` with `M_i ≽ 0`, `β_i + (1/ε_i)⟨Ω, M_i⟩ ≤ 0` and
`M_i − [[0, ½y_i(x)], [½y_i(x)ᵀ, y_i⁰(x) − β_i]] ≽ 0`.

The scalar constraint `β_i + (1/ε_i)⟨Ω, M_i⟩ ≤ 0` is encoded as
`ε_i β_i + ⟨Ω, M_i⟩ ≤ 0 ∧ β_i ≤ 0`. For `ε_i > 0` the two are equivalent (`⟨Ω, M_i⟩ ≥ 0`
because `Ω ≻ 0` and `M_i ≽ 0`); at `ε_i = 0`, which `ℰ` allows, the encoding is the
extended-real reading `(1/0)·0 = 0`, `(1/0)·t = +∞` for `t > 0`, i.e. `⟨Ω, M_i⟩ = 0` and
`β_i ≤ 0`, and it avoids Lean's `1/0 = 0`. -/
def ZB {m n k : ℕ} (D : DRJointCC.Joint.JCCData m n k) (μ : Fin k → ℝ)
    (Sig : Matrix (Fin k) (Fin k) ℝ) (e : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, ∃ (β : ℝ) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ),
    M.PosSemidef ∧
      e i * β + DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M ≤ 0 ∧
      β ≤ 0 ∧
      (M - ConvexOptimization.symQuadBlock 0 ((1 / 2 : ℝ) • DRJointCC.Joint.y D i x)
        (DRJointCC.Joint.y0 D i x - β)).PosSemidef}

end DRJointCC.Individual.Supplement


