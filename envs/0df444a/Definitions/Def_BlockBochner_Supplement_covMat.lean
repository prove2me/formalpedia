-- Prove2me | Definitions.Def_BlockBochner_Supplement_covMat
-- name    : BlockBochner_Supplement_covMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:31:27.835369+00:00
-- url     : https://prove2.me/theorems/fdc386c9-07b7-4a35-89b0-7b61e4703e0f
-- title:
--   Covariance matrix $\Sigma=(\mathrm{Cov}_\mu(X_i,X_j))$
-- statement:
--   For $X\sim\mu$ and $X_i=\mathbf 1\{i\in X\}$, the covariance matrix is
--   $$
--   \Sigma=(\mathrm{Cov}_\mu(X_i,X_j))_{i,j\in E},\qquad \Sigma_{ij}=p_{ij}-p_ip_j,
--   $$
--   with diagonal $\Sigma_{ii}=p_i-p_i^2=\mathrm{Var}_\mu(X_i)$.
--
--   **Formalization Note** Built from `inclProb`; on the diagonal $\{i,i\}=\{i\}$, so $p_{ii}=p_i$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 5, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_BlockBochner_Supplement_inclProb

namespace BlockBochner.Supplement

/-- **Covariance matrix `Σ`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 5, p.30:
`Σ = (Cov_µ(X_i, X_j))_{i,j∈E}`, where `X_i = 1{i∈X}`, `X ∼ µ`. Entrywise
`Σ_ij = p_ij − p_i p_j`; on the diagonal `Σ_ii = p_i − p_i² = Var_µ(X_i)`.

**Formalization Note** Built from `inclProb`: `p_ij = inclProb I lam {i, j}` (which is `p_i` when
`i = j`, since `{i, i} = {i}`). -/
noncomputable def covMat {α : Type*} [Fintype α] [DecidableEq α] (I : Finset α → Prop)
    (lam : α → ℝ) : Matrix α α ℝ :=
  fun i j => inclProb I lam {i, j} - inclProb I lam {i} * inclProb I lam {j}

end BlockBochner.Supplement


