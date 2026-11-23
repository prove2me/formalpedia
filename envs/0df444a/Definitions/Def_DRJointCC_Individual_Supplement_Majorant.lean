-- Prove2me | Definitions.Def_DRJointCC_Individual_Supplement_Majorant
-- name    : DRJointCC_Individual_Supplement_Majorant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:26:49.292018+00:00
-- url     : https://prove2.me/theorems/973ef453-28c0-4df1-8167-d8d5aa8e4fad
-- title:
--   (36)–(38), p. 18 — the quadratic-majorant approximation $\mathcal Z_Q^{\mathrm{JCC}}(\alpha)$
-- statement:
--   Throughout, $\mathcal P$ is the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, $\Omega=\begin{bmatrix}\Sigma+\mu\mu^\top&\mu\\\mu^\top&1\end{bmatrix}$ is the second-order moment matrix, $\langle X,Y\rangle=\mathrm{Tr}(XY)$, and $\epsilon\in(0,1)$.
--
--   For the joint chance constraint with rows $y_i^0(x)+y_i(x)^\top\tilde\xi\le0$, $i=1,\dots,m$, and scaling parameters $\alpha\in\mathbb R^m$, a **quadratic majorant** is a function $q(\xi)=\xi^\top Q\xi+\xi^\top q+q^0$ with $Q\in\mathbb S^k$, $q\in\mathbb R^k$, $q^0\in\mathbb R$ such that
--
--   $$
--   q(\xi)\ge\alpha_i\big(y_i^0(x)+y_i(x)^\top\xi\big)\qquad\forall\xi\in\mathbb R^k,\ i=1,\dots,m. \tag{36}
--   $$
--
--   The **quadratic-majorant approximation** is
--
--   $$
--   \mathcal Z_Q^{\mathrm{JCC}}(\alpha)=\Big\{x\in\mathbb R^n:\ \exists\,Q\in\mathbb S^k,\ q\in\mathbb R^k,\ q^0\in\mathbb R \text{ such that } q \text{ satisfies (36) and } \inf_{\mathbb P\in\mathcal P}\mathbb P\big(\tilde\xi^\top Q\tilde\xi+\tilde\xi^\top q+q^0\le0\big)\ge1-\epsilon\Big\}. \tag{38}
--   $$
--
--   Replacing the scaled max-function of the joint chance constraint by such a majorant gives a robust individual quadratic chance constraint (37); Theorems 3.4 and 3.5 show this approximation coincides with the worst-case CVaR approximation.
--
--   **Formalization Note** (36) is used in its row-by-row form, which the paper states as equivalent to the max form. $Q\in\mathbb S^k$ is the hypothesis `Q.IsSymm`.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 18, (36), (37), (38)

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual.Supplement

/-- The quadratic-majorant approximation `𝒵_Q^JCC(α)`, (36)–(38), p. 18: `x` belongs to it iff
there are `Q ∈ 𝕊^k`, `q ∈ ℝ^k`, `q⁰ ∈ ℝ` such that `q(ξ) = ξᵀQξ + ξᵀq + q⁰` satisfies
(36) `q(ξ) ≥ α_i (y_i⁰(x) + y_i(x)ᵀξ)` for all `ξ ∈ ℝ^k` and all `i`, and
(37) `inf_{ℙ ∈ 𝒫} ℙ(ξ̃ᵀQξ̃ + ξ̃ᵀq + q⁰ ≤ 0) ≥ 1 − ε`. -/
def ZQ {m n k : ℕ} (D : DRJointCC.Joint.JCCData m n k) (μ : Fin k → ℝ)
    (Sig : Matrix (Fin k) (Fin k) ℝ) (ε : ℝ) (α : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ (Q : Matrix (Fin k) (Fin k) ℝ) (q : Fin k → ℝ) (q0 : ℝ),
    Q.IsSymm ∧
      (∀ (ξ : Fin k → ℝ) (i : Fin m),
        α i * (DRJointCC.Joint.y0 D i x + DRJointCC.Joint.y D i x ⬝ᵥ ξ) ≤
          ξ ⬝ᵥ Q.mulVec ξ + ξ ⬝ᵥ q + q0) ∧
      ENNReal.ofReal (1 - ε) ≤
        ⨅ P ∈ DRJointCC.Individual.ambiguitySet μ Sig,
          P {ξ | ξ ⬝ᵥ Q.mulVec ξ + ξ ⬝ᵥ q + q0 ≤ 0}}

end DRJointCC.Individual.Supplement


