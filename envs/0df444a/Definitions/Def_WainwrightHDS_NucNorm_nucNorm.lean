-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_nucNorm
-- name    : WainwrightHDS_NucNorm_nucNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:26:04.558906+00:00
-- url     : https://prove2.me/theorems/795c725f-2884-4e9d-b649-2085a6677cef
-- title:
--   Nuclear norm $|||\Theta|||_{\mathrm{nuc}}=\sum_{j=1}^{d'}\sigma_j(\Theta)$
-- statement:
--   For $\Theta\in\mathbb R^{d_1\times d_2}$ with singular values $\sigma_1(\Theta)\ge\dots\ge\sigma_{d'}(\Theta)\ge0$, $d'=\min\{d_1,d_2\}$, the **nuclear norm** is
--
--   $$
--   |||\Theta|||_{\mathrm{nuc}} \;=\; \sum_{j=1}^{d'} \sigma_j(\Theta).
--   $$
--
--   It is the $\ell_1$-norm of the vector of singular values and the standard convex relaxation of the rank; it is the regularizer of the estimator (10.16).
--
--   **Formalization Note** The sum runs over the 0-based indices $0,\dots,d'-1$ of `singVal`.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, p. 268 (PDF p. 288), Eq. (9.19); p. 313 (PDF p. 333), Eq. (10.5)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_singVal

namespace WainwrightHDS.NucNorm

/-- **Nuclear norm** `|||Θ|||_nuc = Σ_{j=1}^{d'} σ_j(Θ)`, `d' = min{d₁, d₂}`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, p. 268 (PDF p. 288), Eq. (9.19), and p. 313 (PDF p. 333), Eq. (10.5).

Formalization Note: the book's `j = 1, …, d'` is `j ∈ Finset.range (min d₁ d₂)` with 0-based
`singVal`. -/
noncomputable def nucNorm {d₁ d₂ : ℕ} (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ :=
  ∑ j ∈ Finset.range (min d₁ d₂), singVal j Θ

end WainwrightHDS.NucNorm


