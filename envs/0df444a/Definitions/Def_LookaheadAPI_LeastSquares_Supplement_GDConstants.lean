-- Prove2me | Definitions.Def_LookaheadAPI_LeastSquares_Supplement_GDConstants
-- name    : LookaheadAPI_LeastSquares_Supplement_GDConstants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:52:55.383395+00:00
-- url     : https://prove2.me/theorems/1d5f0cb1-3a4f-4242-867c-c44bfd3d56f6
-- title:
--   Assumption 2 and the constants $\alpha_{GD,\gamma}$, $\sigma_{\min,\Phi}$, $\beta$ and $\tau$ of (12) for gradient-descent policy evaluation
-- statement:
--   This module defines the quantities in which the paper states the error of Algorithm 4, and Assumption 2.
--
--   Let $\Phi\in\mathbb R^{|\mathcal S|\times d}$ be the feature matrix and $\mathcal D_k$, $k\ge0$, the evaluation sets. Write $\lambda_i(G)$ for the eigenvalues of a symmetric matrix $G$, $\|\cdot\|_\infty$ for the induced $\infty$-norm (maximum absolute row sum) and $\delta_{FV}$, $\delta_{app}$ for the constants of Theorem 1 (published definition `LSOperator`).
--
--   1. The **Euclidean norm** $\|\theta\|_2=(\sum_i\theta_i^2)^{1/2}$ of a parameter vector.
--   2. The **contraction factor of gradient descent**
--   $$\alpha_{GD,\gamma}:=\sup_k\max_i\big|1-\gamma\lambda_i(\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k})\big|.$$
--   3. The **smallest singular value** $\sigma_{\min,\Phi}$ of $\Phi$.
--   4. With $c:=\sqrt{|\mathcal S|}\,\|\Phi\|_\infty/\sigma_{\min,\Phi}$, the constants of (12):
--   $$\beta:=\alpha^{m+H-1}\delta_{FV}+c\,\alpha_{GD,\gamma}^\eta\big(\alpha^{m+H-1}\delta_{FV}+1\big),$$
--   $$\tau:=\big(1+c\,\alpha_{GD,\gamma}^\eta\big)\Big(\frac{\alpha^m+\alpha^{m+H-1}}{1-\alpha}\delta_{FV}+\delta_{app}+\delta_{FV}\varepsilon_{PE}\Big)+\frac{\sqrt{|\mathcal S|}\,\|\Phi\|_\infty}{(1-\alpha)\sigma_{\min,\Phi}}\alpha_{GD,\gamma}^\eta .$$
--   5. **Assumption 2**: the step size $\gamma$, the rollout length $m$, the number of gradient steps $\eta$ and the lookahead depth $H$ satisfy
--   $$\gamma<\frac{1}{d\,\inf_k\|\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k}\|_\infty^2},\qquad m+H>1+\frac{\log(2\delta_{FV})}{\log(1/\alpha)},\qquad \eta>\frac{\log\big(3\sqrt{|\mathcal S|}\,\|\Phi\|_\infty/\sigma_{\min,\Phi}\big)}{\log(1/\alpha_{GD,\gamma})}.$$
--
--   The constants $\beta$ and $\tau$ replace those of Theorem 1 when the least-squares fit is replaced by $\eta$ gradient steps; as $\eta\to\infty$ with $\alpha_{GD,\gamma}<1$ they reduce to Theorem 1's.
--
--   **Formalization Note** The eigenvalues are Mathlib's eigenvalues of the symmetric Gram matrix, listed with multiplicity in no particular order; the maximum over $i$ does not depend on the order. The supremum over $k$ is a real supremum over finitely many values (there are finitely many subsets of $\mathcal S$); for $d=0$ the maximum over the empty index set is $0$. $\sigma_{\min,\Phi}$ is the published `GaussianMatrix.sMin`, $\inf\{\|\Phi x\|_2:\|x\|_2=1\}$, which is the smallest singular value of $\Phi$ whenever $d\le|\mathcal S|$ (always the case under Assumption 1). The first clause of Assumption 2 is written $\gamma\cdot d\inf_k\|\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k}\|_\infty^2<1$: this is the printed inequality when the denominator is positive, and imposes nothing when the denominator is $0$ (reading $1/0$ as $+\infty$). As printed, $\gamma$ has no lower bound. Logarithms are real logarithms, with Lean's conventions $\log x=\log|x|$ and $\log0=0$, and division by $0$ gives $0$.
-- source:
--   arXiv:2109.13419v7, pp. 16–17, Assumption 2 (definitions of α_GD,γ and σ_min,Φ); p. 17, eq. (12) (β, τ); p. 26, Appendix E (β, τ)

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms

namespace LookaheadAPI.LeastSquares.Supplement

open Matrix

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]

/-- The Euclidean norm `‖θ‖_2 = (∑_i θ_i²)^{1/2}` of a parameter vector (Lean's default norm on
`Fin d → ℝ` is the sup norm). -/
noncomputable def norm2 {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, θ i ^ 2)

omit [Fintype S] [DecidableEq S] in
/-- The Gram matrix `Φ_𝒟^⊤ Φ_𝒟` is symmetric. -/
theorem gram_isHermitian {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : Finset S) :
    (gram Φ D).IsHermitian := by
  have h := isHermitian_conjTranspose_mul_self (featuresOn Φ D)
  simpa [gram, Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- The eigenvalues `λ_i(Φ_𝒟^⊤ Φ_𝒟)`, `i = 1, …, d`, of the symmetric Gram matrix, listed with
multiplicity (Mathlib's `IsHermitian.eigenvalues`; only their multiset matters below). -/
noncomputable def gramEig {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : Finset S) : Fin d → ℝ :=
  (gram_isHermitian Φ D).eigenvalues

/-- `α_{GD,γ} := sup_k max_i |1 − γ λ_i(Φ_{𝒟_k}^⊤ Φ_{𝒟_k})|` (Assumption 2, p. 17). The supremum
over `k` ranges over finitely many values (there are finitely many subsets of `𝒮`), so it is a
real number; for `d = 0` it is `0`. -/
noncomputable def alphaGD {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S) (γ : ℝ) : ℝ :=
  ⨆ k : ℕ, ⨆ i : Fin d, |1 - γ * gramEig Φ (D k) i|

/-- `σ_{min,Φ}`, the smallest singular value of the `|𝒮| × d` feature matrix `Φ` (Assumption 2,
p. 17): the published `GaussianMatrix.sMin Φ = inf {‖Φx‖_2 : ‖x‖_2 = 1}`. -/
noncomputable def sigmaMin {d : ℕ} (Φ : Matrix S (Fin d) ℝ) : ℝ :=
  GaussianMatrix.sMin Φ

/-- The factor `√|𝒮| ‖Φ‖_∞ / σ_{min,Φ}` of (12). -/
noncomputable def gdFactor {d : ℕ} (Φ : Matrix S (Fin d) ℝ) : ℝ :=
  Real.sqrt (Fintype.card S) * opNormInf Φ / sigmaMin Φ

/-- `β := α^{m+H−1} δ_FV + (√|𝒮| ‖Φ‖_∞/σ_{min,Φ}) α_{GD,γ}^η (α^{m+H−1} δ_FV + 1)`
((12), p. 17; Theorem 2; Appendix E, p. 26). Its first term is the base `betaLS`. -/
noncomputable def betaGD {d : ℕ} (M : MDP S A) (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S)
    (m H : ℕ) (γ : ℝ) (η : ℕ) : ℝ :=
  betaLS M Φ D m H + gdFactor Φ * alphaGD Φ D γ ^ η * (betaLS M Φ D m H + 1)

/-- `τ := (1 + (√|𝒮| ‖Φ‖_∞/σ_{min,Φ}) α_{GD,γ}^η)((α^m + α^{m+H−1})/(1 − α) δ_FV + δ_app
+ δ_FV ε_PE) + (√|𝒮| ‖Φ‖_∞/((1 − α) σ_{min,Φ})) α_{GD,γ}^η` ((12), p. 17; Theorem 2; Appendix E,
p. 26). Its second bracket is the base `tauLS`. -/
noncomputable def tauGD {d : ℕ} (M : MDP S A) (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S)
    (m H : ℕ) (εPE γ : ℝ) (η : ℕ) : ℝ :=
  (1 + gdFactor Φ * alphaGD Φ D γ ^ η) * tauLS M Φ D m H εPE +
    Real.sqrt (Fintype.card S) * opNormInf Φ / ((1 - M.α) * sigmaMin Φ) * alphaGD Φ D γ ^ η

/-- Assumption 2 (pp. 16–17), its three clauses as printed:
`γ < 1/(d inf_k ‖Φ_{𝒟_k}^⊤ Φ_{𝒟_k}‖_∞²)` (written `γ · (d inf_k ‖·‖_∞²) < 1`, which is the printed
inequality when the denominator is positive and imposes nothing when it is `0`, the reading of
`1/0 = +∞`), `m + H > 1 + log(2δ_FV)/log(1/α)` and
`η > log(3√|𝒮| ‖Φ‖_∞/σ_{min,Φ})/log(1/α_{GD,γ})` (real logarithms). `γ` has no lower bound. -/
def Assumption2 {d : ℕ} (M : MDP S A) (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S) (m H : ℕ)
    (γ : ℝ) (η : ℕ) : Prop :=
  γ * ((d : ℝ) * ⨅ k : ℕ, opNormInf (gram Φ (D k)) ^ 2) < 1 ∧
  ((m + H : ℕ) : ℝ) > 1 + Real.log (2 * deltaFV Φ D) / Real.log (1 / M.α) ∧
  (η : ℝ) > Real.log (3 * Real.sqrt (Fintype.card S) * opNormInf Φ / sigmaMin Φ) /
    Real.log (1 / alphaGD Φ D γ)

end LookaheadAPI.LeastSquares.Supplement


