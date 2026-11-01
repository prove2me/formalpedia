-- Prove2me | Definitions.Def_ProjFPOracle_En
-- name    : ProjFPOracle_En
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:40.216826+00:00
-- url     : https://prove2.me/theorems/f23729ae-76f8-4893-99b2-c3d3e613b408
-- title:
--   The leading statistical term $\mathcal E_n(M,\Sigma^*)$
-- statement:
--   For a $d\times d$ matrix $M$ with $I-M$ invertible, a covariance matrix $\Sigma^*$ and a sample size $n$,
--   $$
--   \mathcal E_n(M,\Sigma^*):=\frac{\operatorname{trace}\big((I-M)^{-1}\Sigma^*(I-M)^{-\top}\big)}{n}.
--   $$
--   It is the dominant statistical error of Theorem 1, the local complexity of estimating $\bar v$, and the paper shows it is information-theoretically optimal.
--
--   **Formalization Note** $(I-M)^{-1}$ is Mathlib's matrix inverse (the true inverse under $\kappa(M)<1$, assumed by every statement); $n$ is cast to a real.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, §3.1.1, p.12, Eq. (27a)

import Mathlib

namespace ProjFPOracle

/-- **The leading statistical term `𝓔_n(M, Σ^*)`** (Mou, Pananjady & Wainwright, *Optimal Oracle
Inequalities for Projected Fixed-Point Equations*, arXiv:2012.05299v1, Eq. (27a), p.12):
`𝓔_n(M, Σ^*) := trace((I − M)⁻¹ Σ^* (I − M)⁻ᵀ) / n`.

**Formalization Note** `(I − M)⁻¹` is Mathlib's matrix inverse (the true inverse under `κ(M) < 1`,
which every statement of the mission assumes); `n` is cast to `ℝ`, and every statement has `n ≥ 2`. -/
noncomputable def En {d : ℕ} (M Sig : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) : ℝ :=
  Matrix.trace ((1 - M)⁻¹ * Sig * ((1 - M)⁻¹).transpose) / n

end ProjFPOracle


