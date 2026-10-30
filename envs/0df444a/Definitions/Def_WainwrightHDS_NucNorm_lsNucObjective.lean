-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_lsNucObjective
-- name    : WainwrightHDS_NucNorm_lsNucObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:27:36.488546+00:00
-- url     : https://prove2.me/theorems/f53202f2-f0f2-4ec3-abbb-6d685b6f0192
-- title:
--   Nuclear-norm regularized least-squares objective (10.16)
-- statement:
--   Given observations $(y,\mathfrak X_n)$ with $y\in\mathbb R^n$ and a regularization parameter $\lambda_n$, the **nuclear-norm regularized least-squares objective** is
--
--   $$
--   \Theta\ \longmapsto\ \frac{1}{2n}\,\|y-\mathfrak X_n(\Theta)\|_2^2 \;+\; \lambda_n\,|||\Theta|||_{\mathrm{nuc}}, \qquad \Theta\in\mathbb R^{d_1\times d_2}.
--   $$
--
--   The estimator $\widehat\Theta$ of (10.16) is any global minimizer of this objective.
--
--   **Formalization Note** $\|v\|_2^2$ is written $\sum_i v_i^2$. The book's $\lambda_n>0$ is a hypothesis of the theorems, not part of the definition. In Lean $1/(2\cdot 0)=0$; the theorems that use the objective exclude $n=0$ through their hypotheses.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §10.2.2, p. 319 (PDF p. 339), Eq. (10.16)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_obsOp
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm

namespace WainwrightHDS.NucNorm

/-- **Nuclear-norm regularized least-squares objective**
`Θ ↦ (1/(2n)) ‖y − 𝔛_n(Θ)‖₂² + λ_n |||Θ|||_nuc`, the program (10.16).
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.2.2, p. 319 (PDF p. 339), Eq. (10.16).

Formalization Note: `‖v‖₂²` is written `Σ_i v_i²`; `λ_n` is the argument `lam` (`λ` is a Lean
keyword). The book's `λ_n > 0` is a hypothesis of the theorems that use the objective. With
`n = 0` Lean reads `1/(2·0) = 0`; the theorems using it exclude that case through their other
hypotheses. -/
noncomputable def lsNucObjective {n d₁ d₂ : ℕ} (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ)
    (y : Fin n → ℝ) (lam : ℝ) (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ :=
  1 / (2 * (n : ℝ)) * ∑ i, (y i - obsOp X Θ i) ^ 2 + lam * nucNorm Θ

end WainwrightHDS.NucNorm


