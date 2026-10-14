-- Prove2me | Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
-- name    : LookaheadAPI_LeastSquares_LSOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:12.919711+00:00
-- url     : https://prove2.me/theorems/e2fad0c7-0a3e-4895-92d1-b6087229055a
-- title:
--   The least-squares operator $\mathcal M_{\mathcal D}=\Phi(\Phi_{\mathcal D}^\top\Phi_{\mathcal D})^{-1}\Phi_{\mathcal D}^\top\mathcal P_{\mathcal D}$, $\delta_{FV}$ and $\delta_{app}$
-- statement:
--   This module defines the linear-algebra objects of Section 3.1 and Theorem 1.
--
--   Each state $i\in\mathcal S$ carries a **feature vector** $\phi(i)\in\mathbb R^d$, and $\Phi$ is the $|\mathcal S|\times d$ matrix whose rows are the feature vectors. For a set of states $\mathcal D\subseteq\mathcal S$:
--
--   1. $\Phi_{\mathcal D}$ is the matrix whose rows are the feature vectors of the states in $\mathcal D$;
--   2. $\mathcal P_{\mathcal D}$ is the $0/1$ matrix such that $\mathcal P_{\mathcal D}J$ is the vector of the entries $J(i)$, $i\in\mathcal D$;
--   3. the **least-squares operator** of (6) is
--   $$\mathcal M_{\mathcal D}=\Phi\,(\Phi_{\mathcal D}^\top\Phi_{\mathcal D})^{-1}\Phi_{\mathcal D}^\top\mathcal P_{\mathcal D}\in\mathbb R^{|\mathcal S|\times|\mathcal S|};$$
--   4. $\|M\|_\infty$ is the operator norm induced by $\|\cdot\|_\infty$, i.e. the maximum absolute row sum $\max_i\sum_j|M_{ij}|$.
--
--   For a sequence of evaluation sets $\mathcal D_0,\mathcal D_1,\dots$ (writing $\mathcal M_k$ for $\mathcal M_{\mathcal D_k}$) it defines
--   $$\delta_{FV}=\sup_k\|\mathcal M_k\|_\infty,\qquad \delta_{app}=\sup_{k,\mu}\|\mathcal M_kJ^{\mu}-J^{\mu}\|_\infty ,$$
--   the second supremum ranging over all iterations $k$ and all deterministic policies $\mu$.
--
--   The constant $\delta_{FV}$ measures how much a least-squares fit on $\mathcal D_k$ can amplify errors in sup norm, and $\delta_{app}$ measures how well the feature space represents value functions; both enter the error bound of Theorem 1.
--
--   **Formalization Note** The Gram matrix $\Phi_{\mathcal D}^\top\Phi_{\mathcal D}$ is `gram Φ D`; Assumption 1's rank condition is $\det(\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k})\neq0$. Lean's matrix inverse is $0$ on a singular matrix, so every statement that uses $\mathcal M_{\mathcal D_k}$ assumes this for every $k$. Equation (6) attaches $\mathcal D_k$ to $\mathcal M_{k+1}$ while Theorem 1 attaches it to $\mathcal M_k$; both suprema range over the same matrices, so one function $\mathcal D\mapsto\mathcal M_{\mathcal D}$ is used. The suprema are real suprema of finitely many values (there are finitely many subsets of $\mathcal S$ and finitely many policies), so they are maxima.
-- source:
--   arXiv:2109.13419v7, p. 10, Section 3.1, eq. (6); p. 14, Theorem 1 (δ_FV, δ_app)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP

namespace LookaheadAPI.LeastSquares

open Matrix

variable {S A : Type*} [Fintype S] [DecidableEq S]

/-- The induced `∞`-norm `‖M‖_∞` of a matrix: Mathlib's `ℓ^∞` operator norm, which is the maximum
absolute row sum `max_i ∑_j |M_{ij}|` (`Matrix.linfty_opNorm_def`) and the operator norm of `M`
acting on `(ℝ^n, ‖·‖_∞)`. -/
noncomputable def opNormInf {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : ℝ :=
  @Norm.norm _ (Matrix.linftyOpNormedAddCommGroup (m := m) (n := n) (α := ℝ)).toNorm M

/-- `Φ_𝒟`: the matrix whose rows are the feature vectors `φ(i)` of the states `i ∈ 𝒟`
(Section 3.1, p. 10). `Φ : 𝒮 × d` has the feature vector `φ(i) ∈ ℝ^d` as its row `i`. -/
def featuresOn {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : Finset S) : Matrix D (Fin d) ℝ :=
  Φ.submatrix (fun i : D => (i : S)) id

/-- `𝒫_𝒟`: the `0/1` matrix such that `𝒫_𝒟 J` is the vector of entries `J(i)`, `i ∈ 𝒟`
(Section 3.1, p. 10). -/
def restrictTo (D : Finset S) : Matrix D S ℝ :=
  fun i j => if (i : S) = j then 1 else 0

/-- The Gram matrix `Φ_𝒟^⊤ Φ_𝒟` of the features of the states in `𝒟`. Assumption 1's rank
condition `rank {φ(i)}_{i ∈ 𝒟} = d` is `det (Φ_𝒟^⊤ Φ_𝒟) ≠ 0`. -/
def gram {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : Finset S) : Matrix (Fin d) (Fin d) ℝ :=
  (featuresOn Φ D)ᵀ * featuresOn Φ D

/-- The least-squares operator `ℳ_𝒟 = Φ (Φ_𝒟^⊤ Φ_𝒟)^{-1} Φ_𝒟^⊤ 𝒫_𝒟` of (6) (p. 10). For an
iteration with evaluation set `𝒟_k` it is the paper's `ℳ_{k+1}` in (6) and `ℳ_k` in Theorem 1's
`δ_FV` (both range over the same matrices). Mathlib's `⁻¹` is the true inverse only when
`det (Φ_𝒟^⊤ Φ_𝒟) ≠ 0`; every statement using `lsOp` assumes this. -/
noncomputable def lsOp {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : Finset S) : Matrix S S ℝ :=
  Φ * (gram Φ D)⁻¹ * (featuresOn Φ D)ᵀ * restrictTo D

/-- `δ_FV := sup_k ‖ℳ_k‖_∞` (Theorem 1, p. 14) for the sequence of evaluation sets `𝒟_k`. The
supremum is over a finite set of values (there are finitely many subsets of `𝒮`). -/
noncomputable def deltaFV {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S) : ℝ :=
  ⨆ k : ℕ, opNormInf (lsOp Φ (D k))

/-- `δ_app := sup_{k, μ_k} ‖ℳ_k J^{μ_k} − J^{μ_k}‖_∞` (Theorem 1, p. 14): the supremum over all
iterations `k` and all deterministic policies `μ : 𝒮 → 𝒜`. -/
noncomputable def deltaApp [Fintype A] [DecidableEq A] {d : ℕ} (M : MDP S A)
    (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S) : ℝ :=
  ⨆ k : ℕ, ⨆ μ : S → A, ‖lsOp Φ (D k) *ᵥ valueOf M μ - valueOf M μ‖

end LookaheadAPI.LeastSquares


