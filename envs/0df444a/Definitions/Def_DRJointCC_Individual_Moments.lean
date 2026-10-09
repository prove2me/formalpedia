-- Prove2me | Definitions.Def_DRJointCC_Individual_Moments
-- name    : DRJointCC_Individual_Moments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:07.651999+00:00
-- url     : https://prove2.me/theorems/1bb921e6-c6c8-48d6-8a98-81944da094bb
-- title:
--   §2, pp. 4–5, (6) — the moment set 𝒫, the moment matrix Ω, CVaR, worst-case CVaR and worst-case expectation
-- statement:
--   This module fixes the standing setting of §2 of Zymler, Kuhn and Rustem and the objects shared by all results of the paper.
--
--   Let $\tilde\xi$ be a random vector in $\mathbb R^k$, let $\mu\in\mathbb R^k$ be a mean vector and $\Sigma\in\mathbb S^k$ a covariance matrix. The module defines:
--
--   1. **The moment ambiguity set** $\mathcal P$: the set of all probability measures $\mathbb P$ on $\mathbb R^k$ with finite second moments, mean $\mathbb E_{\mathbb P}[\tilde\xi]=\mu$ and covariance $\mathbb E_{\mathbb P}[(\tilde\xi-\mu)(\tilde\xi-\mu)^\top]=\Sigma$.
--   2. **The second-order moment matrix**
--   $$
--   \Omega=\begin{bmatrix}\Sigma+\mu\mu^\top & \mu\\ \mu^\top & 1\end{bmatrix}\in\mathbb S^{k+1}.
--   $$
--   3. **The lifted quadratic** $[\xi^\top\ 1]\,M\,[\xi^\top\ 1]^\top$ of a matrix $M\in\mathbb S^{k+1}$ at $\xi\in\mathbb R^k$, and the **trace scalar product** $\langle X,Y\rangle=\operatorname{Tr}(XY)$.
--   4. **Conditional Value-at-Risk** (6): for a loss $L:\mathbb R^k\to\mathbb R$, a probability measure $\mathbb P$ and a tolerance $\epsilon$,
--   $$
--   \mathbb P\text{-}\mathrm{CVaR}_\epsilon(L(\tilde\xi))=\inf_{\beta\in\mathbb R}\Big\{\beta+\frac1\epsilon\,\mathbb E_{\mathbb P}\big((L(\tilde\xi)-\beta)^+\big)\Big\},
--   $$
--   where $x^+=\max\{x,0\}$.
--   5. **The worst-case CVaR** $\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon(L(\tilde\xi))$.
--   6. **The worst-case expectation of a positive part** $\theta_{\mathrm{wc}}(f)=\sup_{\mathbb P\in\mathcal P}\mathbb E_{\mathbb P}\big((f(\tilde\xi))^+\big)$ of Lemma A.1.
--
--   These are the objects in which the paper's exactness results and its semidefinite reformulations are stated.
--
--   **Formalization Note** $\mathbb R^k$ is `Fin k → ℝ`; the $(k+1)$-dimensional matrices are indexed by `Fin k ⊕ Unit` with the extra coordinate last, and $\Omega$ is built with the published `ConvexOptimization.symQuadBlock`. Membership in $\mathcal P$ uses the published `MomentDRO.Conf.HasSecondMoments` (a probability measure with every coordinate in $L^2$), `meanVec` and `covMat`, so the mean and covariance are genuine integrals. CVaR, the worst-case CVaR and $\theta_{\mathrm{wc}}$ take values in the extended reals: the expectation of a positive part is a lower Lebesgue integral and may be $+\infty$, and a supremum over $\mathcal P$ may be $+\infty$. Over the empty set the supremum is $-\infty$; the theorems carry the paper's standing assumption $\Sigma\succ0$, under which $\mathcal P$ is nonempty. The variable is named `Sig` because `Σ` is a reserved token in Lean.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, pp. 4–5, Notation, Distributional Assumptions and (6); p. 6, (7)–(8); p. 30, Lemma A.1

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_ConvexOptimization_quadraticForms

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual

/-- The moment ambiguity set `𝒫` (Zymler–Kuhn–Rustem, p. 5): all probability measures on `ℝ^k`
with finite second moments, mean vector `μ` and covariance matrix `Sig`. -/
def ambiguitySet {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) :
    Set (Measure (Fin k → ℝ)) :=
  {P | MomentDRO.Conf.HasSecondMoments P ∧ MomentDRO.Conf.meanVec P = μ ∧
    MomentDRO.Conf.covMat P = Sig}

/-- The second-order moment matrix `Ω = [[Σ + μμᵀ, μ], [μᵀ, 1]]` (p. 5), indexed by
`Fin k ⊕ Unit` with the extra coordinate last. -/
noncomputable def momentMatrix {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ :=
  ConvexOptimization.symQuadBlock (Sig + Matrix.vecMulVec μ μ) μ 1

/-- The lifted vector `[ξᵀ 1]ᵀ`. -/
def lift {k : ℕ} (ξ : Fin k → ℝ) : Fin k ⊕ Unit → ℝ := Sum.elim ξ (fun _ => 1)

/-- The lifted quadratic `[ξᵀ 1] M [ξᵀ 1]ᵀ`. -/
def liftQuad {k : ℕ} (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (ξ : Fin k → ℝ) : ℝ :=
  lift ξ ⬝ᵥ M.mulVec (lift ξ)

/-- The trace scalar product `⟨X, Y⟩ = Tr(XY)` (p. 4). -/
def frob {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℝ) : ℝ := Matrix.trace (X * Y)

/-- `ℙ-CVaR_ε(L(ξ̃)) = inf_β { β + (1/ε) E_ℙ((L(ξ̃) − β)⁺) }` (6), p. 5, extended-real valued;
the expectation of the positive part is a lower Lebesgue integral, so it may be `+∞`. -/
noncomputable def cvar {k : ℕ} (ε : ℝ) (P : Measure (Fin k → ℝ)) (L : (Fin k → ℝ) → ℝ) : EReal :=
  ⨅ β : ℝ, ((β : EReal) + ((ε⁻¹ : ℝ) : EReal) *
    ((∫⁻ ξ, ENNReal.ofReal (L ξ - β) ∂P : ℝ≥0∞) : EReal))

/-- The worst-case CVaR `sup_{ℙ ∈ 𝒫} ℙ-CVaR_ε(L(ξ̃))` ((7)–(8), p. 6). -/
noncomputable def wcCVaR {k : ℕ} (ε : ℝ) (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (L : (Fin k → ℝ) → ℝ) : EReal :=
  ⨆ P ∈ ambiguitySet μ Sig, cvar ε P L

/-- The worst-case expectation `θ_wc = sup_{ℙ ∈ 𝒫} E_ℙ((f(ξ̃))⁺)` of Lemma A.1, p. 30. -/
noncomputable def wcExpPos {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (f : (Fin k → ℝ) → ℝ) : EReal :=
  ⨆ P ∈ ambiguitySet μ Sig, ((∫⁻ ξ, ENNReal.ofReal (f ξ) ∂P : ℝ≥0∞) : EReal)

end DRJointCC.Individual


