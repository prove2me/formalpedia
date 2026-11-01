-- Prove2me | Definitions.Def_HomotopyProxVM_omegaConst
-- name    : HomotopyProxVM_omegaConst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:53.811725+00:00
-- url     : https://prove2.me/theorems/3c124d4b-bac3-47e7-8c5e-dfea403a80d6
-- title:
--   The contraction factor $\omega$
-- statement:
--   For $\mu_f,L_f,m,L$ as in Theorem 4, the **contraction factor** is
--
--   $$
--   \omega:=\frac1m\sqrt{(L-2\mu_f)m+L_f^2}.
--   $$
--
--   The condition $\omega<1$ is what the theorem asks of the metric bounds $m$ and $L$.
--
--   **Formalization Note** When $p\ge1$, strong convexity and smoothness give $L_f\ge\mu_f$, so with $m\le L$ the radicand is at least $(m-\mu_f)^2\ge0$.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Theorem 4, p.8; Lemma 16, p.24

import Mathlib

namespace HomotopyProxVM

/-- The contraction factor `ω := (1/m) √((L − 2μ_f) m + L_f²)`
(Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Theorem 4, p.8; Lemma 16, p.24).

**Formalization Note.** For `p ≥ 1`, `μ_f`-strong convexity and `L_f`-smoothness give `L_f ≥ μ_f`, so
with `m ≤ L` the radicand is at least `(m − μ_f)² ≥ 0` and `Real.sqrt` returns the true root. -/
noncomputable def omegaConst (μ Lf m L : ℝ) : ℝ :=
  1 / m * Real.sqrt ((L - 2 * μ) * m + Lf ^ 2)

end HomotopyProxVM


