-- Prove2me | Definitions.Def_SparseBatchBandit_IsLassoSelector
-- name    : SparseBatchBandit_IsLassoSelector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:31:31.96541+00:00
-- url     : https://prove2.me/theorems/cd21a707-a103-46c0-a53f-4427661c3374
-- title:
--   Measurable selection of Lasso minimizers
-- statement:
--   The rule `sel` is a measurable selection of minimizers if, for every $m\in[M]$, it is a measurable function of the data, and for all data $(X,y)$ its output minimizes
--
--   $$
--   \theta\mapsto\frac{1}{2|T^{(m)}|}\sum_{t\in T^{(m)}}(r_{t,a_t}-x_{t,a_t}^\top\theta)^2+\lambda_m\|\theta\|_1
--   $$
--
--   over $\mathbb R^d$. This is the update $\hat\theta_m\leftarrow\operatorname{argmin}$ of Algorithm 1.
--
--   **Formalization Note** The argmin need not be unique and the paper names no rule. Measurability makes $\hat\theta_m$ a random vector. A measurable selection exists, for instance the minimizer of least Euclidean norm, so the requirement is not vacuous. The objective is the published `HighDimStat.SparseLinear.IsLagrangianLassoSolution`.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_LassoSelector
import Definitions.Def_SparseBatchBandit_lambdaM
import Definitions.Def_HighDimStat_SparseLinear_IsLagrangianLassoSolution

namespace SparseBatchBandit

/-- `sel` selects a minimizer in the update
`θ̂_m ← argmin_θ (1/(2|T^{(m)}|)) ∑_{t∈T^{(m)}} (r_{t,a_t} − x_{t,a_t}⊤θ)² + λ_m‖θ‖₁`
of Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Algorithm 1, p.16 (PDF 16), and it does so measurably in the data.

**Formalization Note.** The argmin need not be unique and the page names no rule. Measurability is
what makes `θ̂_m` a random vector. A rule with both properties exists, for instance the minimizer of
least `ℓ₂` norm. The objective is `HighDimStat.SparseLinear.IsLagrangianLassoSolution`. -/
def IsLassoSelector {T s₀ M d : ℕ} (K : ℕ) (sel : LassoSelector T s₀ M d) : Prop :=
  ∀ m ∈ Finset.Icc 1 M,
    Measurable (fun p : (Fin (sample T s₀ M m).card → Fin d → ℝ) ×
        (Fin (sample T s₀ M m).card → ℝ) => sel m p.1 p.2) ∧
    ∀ (X : Fin (sample T s₀ M m).card → Fin d → ℝ) (y : Fin (sample T s₀ M m).card → ℝ),
      HighDimStat.SparseLinear.IsLagrangianLassoSolution (Matrix.of X) y
        (lambdaM T d K s₀ M m) (sel m X y)

end SparseBatchBandit


