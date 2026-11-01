-- Prove2me | Definitions.Def_ProjFPOracle_alphaFactor
-- name    : ProjFPOracle_alphaFactor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:53.927852+00:00
-- url     : https://prove2.me/theorems/c89160d6-7c35-42ca-ba13-50da63dbba32
-- title:
--   The approximation factor $\alpha(M,s)$
-- statement:
--   For a real $d\times d$ matrix $M$ with $I_d-M$ invertible and a scalar $s$, the **approximation factor** is
--   $$
--   \alpha(M,s)=1+\lambda_{\max}\Big((I_d-M)^{-1}\big(s^2I_d-MM^\top\big)(I_d-M)^{-\top}\Big),
--   $$
--   where $(I_d-M)^{-\top}$ is the transpose of the inverse. The mission uses it at $s=|||L|||_{\mathbb X}$, the operator norm of $L$ on $\mathbb X$.
--
--   It is the instance-dependent pre-factor in front of the best approximation error $\inf_{v\in\mathbb S}\|v-v^*\|^2$ in Theorem 1, and the paper shows it cannot be improved.
--
--   **Formalization Note** $\lambda_{\max}$ is the published `LowRankMEG.lam · 1` (the matrix is symmetric). $(I_d-M)^{-1}$ is Mathlib's matrix inverse, the true inverse whenever $I_d-M$ is invertible, which holds under $\kappa(M)<1$, assumed by every statement.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, §3.1.1, p.12, Eq. (26)

import Mathlib
import Definitions.Def_LowRankMEG_lam

namespace ProjFPOracle

/-- **The approximation factor `α(M, s)`** (Mou, Pananjady & Wainwright, *Optimal Oracle
Inequalities for Projected Fixed-Point Equations*, arXiv:2012.05299v1, Eq. (26), p.12):
`α(M, s) = 1 + λ_max((I − M)⁻¹ (s² I_d − M Mᵀ) (I − M)⁻ᵀ)`, used with `s = |||L|||_𝕏`.

**Formalization Note** `λ_max` is the published `LowRankMEG.lam · 1` (largest eigenvalue of a real
symmetric matrix; the matrix here is symmetric). `(I − M)⁻¹` is Mathlib's matrix inverse, which is
the true inverse whenever `I − M` is invertible; every statement of the mission assumes
`κ(M) < 1`, under which it is (p.7). `(I − M)⁻ᵀ` is the transpose of the inverse. -/
noncomputable def alphaFactor {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) : ℝ :=
  1 + LowRankMEG.lam ((1 - M)⁻¹ * (s ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) - M * M.transpose) *
    ((1 - M)⁻¹).transpose) 1

end ProjFPOracle


