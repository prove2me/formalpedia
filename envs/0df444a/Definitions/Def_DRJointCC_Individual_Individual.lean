-- Prove2me | Definitions.Def_DRJointCC_Individual_Individual
-- name    : DRJointCC_Individual_Individual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:36.966843+00:00
-- url     : https://prove2.me/theorems/3c69138d-fad8-4736-aa21-737748991d53
-- title:
--   (14), p. 8; (20), p. 10 — worst-case VaR, quadratic losses and the SDP value of (20)
-- statement:
--   This module defines the objects specific to the individual chance constraint of §2.2. Let $\mathcal P$ be the moment set with mean $\mu$ and covariance $\Sigma$, $\Omega$ the second-order moment matrix, $\epsilon$ a tolerance and $L:\mathbb R^k\to\mathbb R$ a loss.
--
--   1. **Worst-Case Value-at-Risk** (14):
--   $$
--   \mathrm{WC\text{-}VaR}_\epsilon(L(\tilde\xi))=\inf_{\gamma\in\mathbb R}\Big\{\gamma:\ \inf_{\mathbb P\in\mathcal P}\mathbb P\big(L(\tilde\xi)\le\gamma\big)\ge1-\epsilon\Big\}.
--   $$
--   2. **Quadratic losses**: $L$ is quadratic if $L(\xi)=\xi^\top Q\xi+q^\top\xi+q^0$ for some $Q\in\mathbb R^{k\times k}$, $q\in\mathbb R^k$ and $q^0\in\mathbb R$. No definiteness is required of $Q$, so nonconvex and nonconcave quadratics are included.
--   3. **The value of the semidefinite program (20)**:
--   $$
--   \inf\Big\{\beta+\frac1\epsilon\langle\Omega,M\rangle:\ \beta\in\mathbb R,\ M\in\mathbb S^{k+1},\ M\succeq0,\ [\xi^\top\ 1]\,M\,[\xi^\top\ 1]^\top+\beta-L(\xi)\ge0\ \ \forall\xi\in\mathbb R^k\Big\}.
--   $$
--
--   The worst-case VaR is the quantity through which the paper proves exactness of the worst-case CVaR approximation, and (20) is the common semidefinite representation of the worst-case VaR and the worst-case CVaR.
--
--   **Formalization Note** Both infima are taken in the extended reals: the infimum over an empty feasible set is $+\infty$, and no real-valued junk value enters. $Q$ is not required to be symmetric; only its symmetric part affects $\xi^\top Q\xi$, so the class of functions is the paper's ($Q\in\mathbb S^k$, p. 12). $M\succeq0$ is `Matrix.PosSemidef`, which includes symmetry.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 8, Theorem 2.2 (ii) and (14); p. 10, (20); p. 12 (form of a quadratic loss)

import Mathlib
import Definitions.Def_DRJointCC_Individual_Moments

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual

/-- The worst-case Value-at-Risk (14), p. 8:
`WC-VaR_ε(L(ξ̃)) = inf { γ ∈ ℝ : inf_{ℙ ∈ 𝒫} ℙ(L(ξ̃) ≤ γ) ≥ 1 − ε }`,
extended-real valued; the infimum of an empty set of `γ` is `+∞`. -/
noncomputable def wcVaR {k : ℕ} (ε : ℝ) (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (L : (Fin k → ℝ) → ℝ) : EReal :=
  ⨅ (γ : ℝ) (_ : ENNReal.ofReal (1 - ε) ≤ ⨅ P ∈ ambiguitySet μ Sig, P {ξ | L ξ ≤ γ}),
    (γ : EReal)

/-- `L` is a (possibly nonconcave) quadratic function of `ξ`: `L(ξ) = ξᵀQξ + qᵀξ + q⁰`
(Theorem 2.2 (ii), p. 8; the form on p. 12). `Q` is not required symmetric: only its
symmetric part matters, so this is the same class of functions. -/
def IsQuadratic {k : ℕ} (L : (Fin k → ℝ) → ℝ) : Prop :=
  ∃ (Q : Matrix (Fin k) (Fin k) ℝ) (q : Fin k → ℝ) (q0 : ℝ),
    ∀ ξ, L ξ = ξ ⬝ᵥ Q.mulVec ξ + q ⬝ᵥ ξ + q0

/-- The optimal value of the SDP (20), p. 10:
`inf { β + (1/ε)⟨Ω, M⟩ : β ∈ ℝ, M ≽ 0, [ξᵀ 1] M [ξᵀ 1]ᵀ + β − L(ξ) ≥ 0 ∀ ξ ∈ ℝ^k }`,
extended-real valued (`+∞` when infeasible). -/
noncomputable def sdpValue20 {k : ℕ} (ε : ℝ) (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (L : (Fin k → ℝ) → ℝ) : EReal :=
  ⨅ (β : ℝ) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ)
    (_ : M.PosSemidef ∧ ∀ ξ, 0 ≤ liftQuad M ξ + β - L ξ),
    (((β + ε⁻¹ * frob (momentMatrix μ Sig) M : ℝ)) : EReal)

end DRJointCC.Individual


